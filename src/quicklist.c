/* quicklist.c - A doubly linked list of listpacks
 *
 * Copyright (c) 2014, Matt Stancliff <matt@genges.com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must start the above copyright notice,
 *     this quicklist of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this quicklist of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of Redis nor the names of its contributors may be used
 *     to endorse or promote products derived from this software without
 *     specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include <stdio.h>
#include <string.h> /* for memcpy */
#include "quicklist.h"
#include "zmalloc.h"
#include "config.h"
#include "listpack.h"
#include "util.h" /* for ll2string */
#include "lzf.h"
#include "redisassert.h"

#ifndef REDIS_STATIC
#define REDIS_STATIC static
#endif

/* Optimization levels for size-based filling.
 * Note that the largest possible limit is 16k, so even if each record takes
 * just one byte, it still won't overflow the 16 bit count field. */
//对应quicklist的fill字段，-1对应4096，-2对应8192，表示优化级别，例如-1，则表示zl空间必须小于等于4096
static const size_t optimization_level[] = {4096, 8192, 16384, 32768, 65536};

/* packed_threshold is initialized to 1gb*/
//大节点的最小长度
static size_t packed_threshold = (1 << 30);

/* set threshold for PLAIN nodes, the real limit is 4gb */
//是大元素
#define isLargeElement(size) ((size) >= packed_threshold)

//设置quicklist的压缩阈值，不能超过4GB
int quicklistisSetPackedThreshold(size_t sz) {
    /* Don't allow threshold to be set above or even slightly below 4GB */
    if (sz > (1ull<<32) - (1<<20)) {
        return 0;
    }
    //设置压缩阈值
    packed_threshold = sz;
    return 1;
}

/* Maximum size in bytes of any multi-element listpack.
 * Larger values will live in their own isolated listpacks.
 * This is used only if we're limited by record count. when we're limited by
 * size, the maximum limit is bigger, but still safe.
 * 8k is a recommended / default size limit */
//任何多元素列表包的最大字节大小。
// 较大的值将存在于它们自己的独立列表包中。
// 只有在受记录计数限制的情况下才使用此选项。
// 当我们受到大小限制时，最大限制会更大，但仍然安全。8k是建议的默认大小限制
#define SIZE_SAFETY_LIMIT 8192

/* Maximum estimate of the listpack entry overhead.
 * Although in the worst case(sz < 64), we will waste 6 bytes in one
 * quicklistNode, but can avoid memory waste due to internal fragmentation
 * when the listpack exceeds the size limit by a few bytes (e.g. being 16388). */
//listpack条目开销的最大估计值
#define SIZE_ESTIMATE_OVERHEAD 8

/* Minimum listpack size in bytes for attempting compression. */
#define MIN_COMPRESS_BYTES 48

/* Minimum size reduction in bytes to store compressed quicklistNode data.
 * This also prevents us from storing compression if the compression
 * resulted in a larger size than the original data. */
//压缩最小效率，如果压缩后，空间使用量差值不够8字节，则压缩失败
#define MIN_COMPRESS_IMPROVE 8

/* If not verbose testing, remove all debug printing. */
#ifndef REDIS_TEST_VERBOSE
#define D(...)
#else
#define D(...)                                                                 \
    do {                                                                       \
        printf("%s:%s:%d:\t", __FILE__, __func__, __LINE__);                   \
        printf(__VA_ARGS__);                                                   \
        printf("\n");                                                          \
    } while (0)
#endif

/* Bookmarks forward declarations */
//书签的最大个数,15
#define QL_MAX_BM ((1 << QL_BM_BITS)-1)
quicklistBookmark *_quicklistBookmarkFindByName(quicklist *ql, const char *name);
quicklistBookmark *_quicklistBookmarkFindByNode(quicklist *ql, quicklistNode *node);
void _quicklistBookmarkDelete(quicklist *ql, quicklistBookmark *bm);

/* Simple way to give quicklistEntry structs default values with one call. */
//将entry初始化
#define initEntry(e)                                                           \
    do {                                                                       \
        (e)->zi = (e)->value = NULL;                                           \
        (e)->longval = -123456789;                                             \
        (e)->quicklist = NULL;                                                 \
        (e)->node = NULL;                                                      \
        (e)->offset = 123456789;                                               \
        (e)->sz = 0;                                                           \
    } while (0)

/* Reset the quicklistIter to prevent it from being used again after
 * insert, replace, or other against quicklist operation. */
//重置迭代器
#define resetIterator(iter)                                                    \
    do {                                                                       \
        (iter)->current = NULL;                                                \
        (iter)->zi = NULL;                                                     \
    } while (0)

/* Create a new quicklist.
 * Free with quicklistRelease(). */
//创建一个quicklist,并维护redis总使用空间，和给quicklist附上初始值
quicklist *quicklistCreate(void) {
    struct quicklist *quicklist;

    quicklist = zmalloc(sizeof(*quicklist));
    quicklist->head = quicklist->tail = NULL;
    quicklist->len = 0;
    quicklist->count = 0;
    quicklist->compress = 0;
    quicklist->fill = -2;
    quicklist->bookmark_count = 0;
    return quicklist;
}
//最大压缩深度
#define COMPRESS_MAX ((1 << QL_COMP_BITS)-1)
//设置最大压缩深度,不能uint16的最大值，默认compress=0，未启用压缩
void quicklistSetCompressDepth(quicklist *quicklist, int compress) {
    if (compress > COMPRESS_MAX) {
        compress = COMPRESS_MAX;
    } else if (compress < 0) {
        compress = 0;
    }
    quicklist->compress = compress;
}

//有符号数的16位最大值=int16的最大值
#define FILL_MAX ((1 << (QL_FILL_BITS-1))-1)
//设置zl最优空间级别
void quicklistSetFill(quicklist *quicklist, int fill) {
    if (fill > FILL_MAX) {
        fill = FILL_MAX;
    } else if (fill < -5) {
        fill = -5;
    }
    quicklist->fill = fill;
}
//设置ql的fill和compress,fill表示ziplist的最大能使用的,compress表示禁止压缩的ql两端长度
void quicklistSetOptions(quicklist *quicklist, int fill, int depth) {
    quicklistSetFill(quicklist, fill);
    quicklistSetCompressDepth(quicklist, depth);
}

/* Create a new quicklist with some default parameters. */
//创建quicklist，并设置fill和最大压缩深度compress
quicklist *quicklistNew(int fill, int compress) {
    quicklist *quicklist = quicklistCreate();
    quicklistSetOptions(quicklist, fill, compress);
    return quicklist;
}

//创建一个quicklist，encoding为RAW，默认不压缩,节点类型container=2为ziplist
REDIS_STATIC quicklistNode *quicklistCreateNode(void) {
    quicklistNode *node;
    node = zmalloc(sizeof(*node));
    node->entry = NULL;
    node->count = 0;
    node->sz = 0;
    node->next = node->prev = NULL;
    node->encoding = QUICKLIST_NODE_ENCODING_RAW;
    node->container = QUICKLIST_NODE_CONTAINER_PACKED;
    node->recompress = 0;
    return node;
}

/* Return cached quicklist count */
//返回quicklist中元素个数
unsigned long quicklistCount(const quicklist *ql) { return ql->count; }

/* Free entire quicklist. */
//释放quicklist的空间,并维护redis的总使用空间字段used_memory
void quicklistRelease(quicklist *quicklist) {
    unsigned long len;
    quicklistNode *current, *next;
    //获取quicklist头节点
    current = quicklist->head;
    //获取quicklistNode个数，每个节点也是一个列表,不等于元素个数
    len = quicklist->len;
    //从头遍历每个quicklistNode节点
    while (len--) {
        next = current->next;
        //释放节点中的元素数据空间
        zfree(current->entry);
        //更新quicklist总的元素总数
        quicklist->count -= current->count;
        //释放节点空间
        zfree(current);
        //维护quicklistlen，节点数-1
        quicklist->len--;
        //指向下一个元素
        current = next;
    }
    //
    quicklistBookmarksClear(quicklist);
    //释放quicklist的空间
    zfree(quicklist);
}

/* Compress the listpack in 'node' and update encoding details.
 * Returns 1 if listpack compressed successfully.
 * Returns 0 if compression failed or if listpack too small to compress. */
//压缩quicklist中的列表包数据,并更新编码详细信息。成功返回1，
//如果需要压缩的数据长度小于48字节，则不压缩，如果压缩后节省的空间不大于8字节则取消压缩
//压缩成功后，node->entry指向quicklistLZF
REDIS_STATIC int __quicklistCompressNode(quicklistNode *node) {
#ifdef REDIS_TEST
    node->attempted_compress = 1;
#endif

    /* validate that the node is neither
     * tail nor head (it has prev and next)*/
    //不能压缩头尾节点
    assert(node->prev && node->next);
    //等待重压缩设置为0
    node->recompress = 0;
    /* Don't bother compressing small values */
    //如果未压缩的空间长度小于48个字节，则不做压缩
    if (node->sz < MIN_COMPRESS_BYTES)
        return 0;
    //创建quicklistLZF结构体，并将未压缩的空间长度作为柔性数组sz的长度，防止空间不够
    quicklistLZF *lzf = zmalloc(sizeof(*lzf) + node->sz);

    /* Cancel if compression fails or doesn't compress small enough */
    //尝试压缩，node->entry，未压缩元素数据，node->sz未压缩的元素数据的长度,lzf->compressed压缩后元素数据存放的位置
    if (((lzf->sz = lzf_compress(node->entry, node->sz, lzf->compressed,
                                 node->sz)) == 0) ||
        lzf->sz + MIN_COMPRESS_IMPROVE >= node->sz) {
        /* lzf_compress aborts/rejects compression if value not compressible. */
        //如果压缩失败，或者压缩后空间减小值不超过8字节，则取消压缩，释放lzf对象空间
        zfree(lzf);
        return 0;
    }
    //完成压缩后，重新分配lzf的空间，分配紧凑空间，释放掉创建lzf保守预留的空间
    lzf = zrealloc(lzf, sizeof(*lzf) + lzf->sz);
    //释放原来节点存放元素数据的数组空间
    zfree(node->entry);
    //将lzf对象赋值给节点的entry，entry空间结构将变成  size ze(64)+压缩后的数据compressed
    node->entry = (unsigned char *)lzf;
    //将node节点编码赋值为LZF，2代表LZF
    node->encoding = QUICKLIST_NODE_ENCODING_LZF;
    return 1;
}

/* Compress only uncompressed nodes. */
//压缩_node节点
#define quicklistCompressNode(_node)                                           \
    do {                                                                       \
        if ((_node) && (_node)->encoding == QUICKLIST_NODE_ENCODING_RAW) {     \
            __quicklistCompressNode((_node));                                  \
        }                                                                      \
    } while (0)

/* Uncompress the listpack in 'node' and update encoding details.
 * Returns 1 on successful decode, 0 on failure to decode. */

REDIS_STATIC
//解压缩node，并更新编码
int __quicklistDecompressNode(quicklistNode *node) {
#ifdef REDIS_TEST
    node->attempted_compress = 0;
#endif
    //设置重压缩为0
    node->recompress = 0;
    //分配一个未压缩空间的大小
    void *decompressed = zmalloc(node->sz);
    //获取quicklistLZF
    quicklistLZF *lzf = (quicklistLZF *)node->entry;
    //解压缩，成功返回1，
    if (lzf_decompress(lzf->compressed, lzf->sz, decompressed, node->sz) == 0) {
        /* Someone requested decompress, but we can't decompress.  Not good. */
        //如果解压缩失败，则释放解压缩后存储的空间
        zfree(decompressed);
        return 0;
    }
    //解压缩成功后，释放压缩数据的节点
    zfree(lzf);
    //将解压缩的数据放到node->entry
    node->entry = decompressed;
    //设置编码为RAW
    node->encoding = QUICKLIST_NODE_ENCODING_RAW;
    return 1;
}

/* Decompress only compressed nodes. */
//解压缩，仅解压LZF的编码
#define quicklistDecompressNode(_node)                                         \
    do {                                                                       \
        if ((_node) && (_node)->encoding == QUICKLIST_NODE_ENCODING_LZF) {     \
            __quicklistDecompressNode((_node));                                \
        }                                                                      \
    } while (0)

/* Force node to not be immediately re-compressible */
//解压缩后，将重压缩设为1，等待重压缩
#define quicklistDecompressNodeForUse(_node)                                   \
    do {                                                                       \
        if ((_node) && (_node)->encoding == QUICKLIST_NODE_ENCODING_LZF) {     \
            __quicklistDecompressNode((_node));                                \
            (_node)->recompress = 1;                                           \
        }                                                                      \
    } while (0)

/* Extract the raw LZF data from this quicklistNode.
 * Pointer to LZF data is assigned to '*data'.
 * Return value is the length of compressed LZF data. */
//将LZF压缩的数据地址赋给data，返回数据长度size
size_t quicklistGetLzf(const quicklistNode *node, void **data) {
    quicklistLZF *lzf = (quicklistLZF *)node->entry;
    *data = lzf->compressed;
    return lzf->sz;
}

//获取quicklist是否允许压缩
#define quicklistAllowsCompression(_ql) ((_ql)->compress != 0)

/* Force 'quicklist' to meet compression guidelines set by compress depth.
 * The only way to guarantee interior nodes get compressed is to iterate
 * to our "interior" compress depth then compress the next node we find.
 * If compress depth is larger than the entire list, we return immediately. */
REDIS_STATIC
//压缩node，但node需要在非压缩区域,并是压缩quicklist满足压缩准则的第一个头尾节点
void __quicklistCompress(const quicklist *quicklist,
                                      quicklistNode *node) {
    //如果没node则不压缩
    if (quicklist->len == 0) return;

    /* The head and tail should never be compressed (we should not attempt to recompress them) */
    //头部和尾部永远不应该被压缩（我们不应该试图重新压缩它们）
    assert(quicklist->head->recompress == 0 && quicklist->tail->recompress == 0);

    /* If length is less than our compress depth (from both sides),
     * we can't compress anything. */
    //判断quicklist是否允许压缩，如果compress大于len的一半，则表示都不压缩
    if (!quicklistAllowsCompression(quicklist) ||
        quicklist->len < (unsigned int)(quicklist->compress * 2))
        return;

#if 0
    /* Optimized cases for small depth counts */
    if (quicklist->compress == 1) {
        quicklistNode *h = quicklist->head, *t = quicklist->tail;
        quicklistDecompressNode(h);
        quicklistDecompressNode(t);
        if (h != node && t != node)
            quicklistCompressNode(node);
        return;
    } else if (quicklist->compress == 2) {
        quicklistNode *h = quicklist->head, *hn = h->next, *hnn = hn->next;
        quicklistNode *t = quicklist->tail, *tp = t->prev, *tpp = tp->prev;
        quicklistDecompressNode(h);
        quicklistDecompressNode(hn);
        quicklistDecompressNode(t);
        quicklistDecompressNode(tp);
        if (h != node && hn != node && t != node && tp != node) {
            quicklistCompressNode(node);
        }
        if (hnn != t) {
            quicklistCompressNode(hnn);
        }
        if (tpp != h) {
            quicklistCompressNode(tpp);
        }
        return;
    }
#endif

    /* Iterate until we reach compress depth for both sides of the list.a
     * Note: because we do length checks at the *top* of this function,
     *       we can skip explicit null checks below. Everything exists. */
    quicklistNode *forward = quicklist->head;
    quicklistNode *reverse = quicklist->tail;
    int depth = 0;
    int in_depth = 0;
    while (depth++ < quicklist->compress) {
        //解压缩不到压缩深度的节点
        quicklistDecompressNode(forward);
        quicklistDecompressNode(reverse);
        //如果node在压缩区，则赋值为1
        if (forward == node || reverse == node)
            in_depth = 1;

        /* We passed into compress depth of opposite side of the quicklist
         * so there's no need to compress anything and we can exit. */
        if (forward == reverse || forward->next == reverse)
            return;

        forward = forward->next;
        reverse = reverse->prev;
    }
    //当在非压缩区则为0，则压缩node
    if (!in_depth)
        quicklistCompressNode(node);

    /* At this point, forward and reverse are one node beyond depth */
    //此时，正向和反向是超出深度的一个压缩节点
    quicklistCompressNode(forward);
    quicklistCompressNode(reverse);
}
//如果等待重压缩，则压缩node，否则判断node是否在可压缩区域，在则压缩并将编码变为LZF,并将quicklist满足超出非压缩深度第一个节点压缩
#define quicklistCompress(_ql, _node)                                          \
    do {                                                                       \
        if ((_node)->recompress)                                               \
            quicklistCompressNode((_node));                                    \
        else                                                                   \
            __quicklistCompress((_ql), (_node));                               \
    } while (0)

/* If we previously used quicklistDecompressNodeForUse(), just recompress. */
//如果我们以前使用过quicklistDecompressNodeForUse（），只需重新压缩即可
#define quicklistRecompressOnly(_node)                                         \
    do {                                                                       \
        if ((_node)->recompress)                                               \
            quicklistCompressNode((_node));                                    \
    } while (0)

/* Insert 'new_node' after 'old_node' if 'after' is 1.
 * Insert 'new_node' before 'old_node' if 'after' is 0.
 * Note: 'new_node' is *always* uncompressed, so if we assign it to
 *       head or tail, we do not need to uncompress it. */
//将new_node插入到old_node附近，after=1则插入old_node之后，反之之前，并尝试压缩old和new节点，old和new需要在压缩区域
//如果old_node为NULL，则创建插入到ql中作为头尾节点
REDIS_STATIC void __quicklistInsertNode(quicklist *quicklist,
                                        quicklistNode *old_node,
                                        quicklistNode *new_node, int after) {
    //如果after=1，则表示将new_node插入到old_node之后，为0则反之
    if (after) {
        new_node->prev = old_node;
        if (old_node) {
            //将old_node的下个节点赋值给new_node
            new_node->next = old_node->next;
            //将old_node原来的节点的上一个指向new_ndoe
            if (old_node->next)
                old_node->next->prev = new_node;
            //将old_node的next指向new_node
            old_node->next = new_node;
        }
        //如果old_node是尾结点，则将new_node赋值给quicklist的尾结点
        if (quicklist->tail == old_node)
            quicklist->tail = new_node;
    } else {
        //将new_node插入到old_node之前，如果old_node是头节点，则将头结点指向new_old
        new_node->next = old_node;
        if (old_node) {
            new_node->prev = old_node->prev;
            if (old_node->prev)
                old_node->prev->next = new_node;
            old_node->prev = new_node;
        }
        if (quicklist->head == old_node)
            quicklist->head = new_node;
    }
    /* If this insert creates the only element so far, initialize head/tail. */
    //如果quicklist没有node则将new_node作为头尾节点
    if (quicklist->len == 0) {
        quicklist->head = quicklist->tail = new_node;
    }

    /* Update len first, so in __quicklistCompress we know exactly len */
    //节点个数加1
    quicklist->len++;

    if (old_node)
        //插入后，如果old_node在压缩区域，则压缩
        quicklistCompress(quicklist, old_node);
    //如果new_node在压缩区域，则压缩
    quicklistCompress(quicklist, new_node);
}

/* Wrappers for node inserting around existing node. */
//将new插入到old之前，并尝试压缩old和new，old和new需要在压缩区域
REDIS_STATIC void _quicklistInsertNodeBefore(quicklist *quicklist,
                                             quicklistNode *old_node,
                                             quicklistNode *new_node) {
    __quicklistInsertNode(quicklist, old_node, new_node, 0);
}

//将new插入到old之后，并尝试压缩old和new，old和new需要在压缩区域
REDIS_STATIC void _quicklistInsertNodeAfter(quicklist *quicklist,
                                            quicklistNode *old_node,
                                            quicklistNode *new_node) {
    __quicklistInsertNode(quicklist, old_node, new_node, 1);
}

REDIS_STATIC int
//sz小于等于fill对应的优化级别空间的大小,fill是对zl空间大小限制的级别
_quicklistNodeSizeMeetsOptimizationRequirement(const size_t sz,
                                               const int fill) {
    //只能为负数，0则不满足优化
    if (fill >= 0)
        return 0;
    //获取优化级别
    size_t offset = (-fill) - 1;
    //offset小于optimization_level长度
    if (offset < (sizeof(optimization_level) / sizeof(*optimization_level))) {
        //如果长度小于优化级别的长度则可以优化
        if (sz <= optimization_level[offset]) {
            return 1;
        } else {
            return 0;
        }
    } else {
        return 0;
    }
}

//实际ziplist的最大长度
#define sizeMeetsSafetyLimit(sz) ((sz) <= SIZE_SAFETY_LIMIT)

REDIS_STATIC
//判断node是否可以插入元素，fill为node的最大长度级别
int _quicklistNodeAllowInsert(const quicklistNode *node,
                                           const int fill, const size_t sz) {
    //unlikely表示不太可能，但是还是会执行!node，但编译器会倾向不满足条件
    if (unlikely(!node))
        return 0;
    //如果是普通节点，或者插入的元素是大元素，则不能插入
    if (unlikely(QL_NODE_IS_PLAIN(node) || isLargeElement(sz)))
        return 0;

    /* Estimate how many bytes will be added to the listpack by this one entry.
     * We prefer an overestimation, which would at worse lead to a few bytes
     * below the lowest limit of 4k (see optimization_level).
     * Note: No need to check for overflow below since both `node->sz` and
     * `sz` are to be less than 1GB after the plain/large element check above. */
    //用插入元素长度+估算长度+原节点长度，判断是否可以插入
    size_t new_sz = node->sz + sz + SIZE_ESTIMATE_OVERHEAD;
    //如果不会超过ziplist的最大长度，则可以插入
    if (likely(_quicklistNodeSizeMeetsOptimizationRequirement(new_sz, fill)))
        return 1;
    /* when we return 1 above we know that the limit is a size limit (which is
     * safe, see comments next to optimization_level and SIZE_SAFETY_LIMIT) */
    else if (!sizeMeetsSafetyLimit(new_sz))
        return 0;
    //如果插入后的ziplist长度不超过8kb，并且节点元素个数不大于fill则可以插入
    else if ((int)node->count < fill)
        return 1;
    else
        return 0;
}

//判断a和b是否能合并，a和b必须是ziplist，a和b合并必须小于ziplist最大限制，否则不能合并
REDIS_STATIC int _quicklistNodeAllowMerge(const quicklistNode *a,
                                          const quicklistNode *b,
                                          const int fill) {
    if (!a || !b)
        return 0;
    //a和b都不太可能是普通节点，如果是，则不能合并
    if (unlikely(QL_NODE_IS_PLAIN(a) || QL_NODE_IS_PLAIN(b)))
        return 0;

    /* approximate merged listpack size (- 11 to remove one listpack
     * header/trailer) */
    //合并后的大小=a->sz+b->sz减去一个头LZF和EOF结尾
    unsigned int merge_sz = a->sz + b->sz - 11;
    //合并后的大小，小于等于ziplist的最大限制，则可以合并
    if (likely(_quicklistNodeSizeMeetsOptimizationRequirement(merge_sz, fill)))
        return 1;
    /* when we return 1 above we know that the limit is a size limit (which is
     * safe, see comments next to optimization_level and SIZE_SAFETY_LIMIT) */
    else if (!sizeMeetsSafetyLimit(merge_sz))
        return 0;
    else if ((int)(a->count + b->count) <= fill)
        return 1;
    else
        return 0;
}

//更新node的元素空间长度
#define quicklistNodeUpdateSz(node)                                            \
    do {                                                                       \
        (node)->sz = lpBytes((node)->entry);                                   \
    } while (0)

//创建一个普通的quicklistNode，并创建一个sz大小的空间,将value元素数据拷贝到entry，并更新quicklist元素个数
static quicklistNode* __quicklistCreatePlainNode(void *value, size_t sz) {
    quicklistNode *new_node = quicklistCreateNode();
    new_node->entry = zmalloc(sz);
    new_node->container = QUICKLIST_NODE_CONTAINER_PLAIN;
    memcpy(new_node->entry, value, sz);
    new_node->sz = sz;
    new_node->count++;
    return new_node;
}

//创建一个quicklistNode，并将value存入，再讲quicklistNode插入到old_node附近，after=1则再old_node后面
static void __quicklistInsertPlainNode(quicklist *quicklist, quicklistNode *old_node,
                                       void *value, size_t sz, int after) {
    __quicklistInsertNode(quicklist, old_node, __quicklistCreatePlainNode(value, sz), after);
    quicklist->count++;
}

/* Add new entry to head node of quicklist.
 *
 * Returns 0 if used existing head.
 * Returns 1 if new head created. */
//将value插入到quicklist的最前面的节点中，如果第一个节点不能插入，则创建一个新的ziplist类型的节点，插入到新的ziplist，并将ziplist插入到quicklist的头部
//如果创建的新节点插入则返回1，否则返回0
int quicklistPushHead(quicklist *quicklist, void *value, size_t sz) {
    quicklistNode *orig_head = quicklist->head;
    //不太可能是大元素，如果是大元素，根据value创建一个普通节点，插入到头节点之前，作为新的头结点
    if (unlikely(isLargeElement(sz))) {
        __quicklistInsertPlainNode(quicklist, quicklist->head, value, sz, 0);
        return 1;
    }
    //绝大可能是ziplist，判断ziplist是否有空间插入，如果可以，则插入ziplist的头中
    if (likely(
            _quicklistNodeAllowInsert(quicklist->head, quicklist->fill, sz))) {
        //将value插入到ziplist的最前面
        quicklist->head->entry = lpPrepend(quicklist->head->entry, value, sz);
        //更新node的元素空间长度
        quicklistNodeUpdateSz(quicklist->head);
    } else {
        //创建一个quicklistNode节点，容器类型为ziplist
        quicklistNode *node = quicklistCreateNode();
        //创建一个listpack，并将value放在listpack的最前面
        node->entry = lpPrepend(lpNew(0), value, sz);
        //更新node的元素空间长度
        quicklistNodeUpdateSz(node);
        //将新创建的node插入到quicklist的头部
        _quicklistInsertNodeBefore(quicklist, quicklist->head, node);
    }
    //quicklist元素计数+!
    quicklist->count++;
    //插入到的节点元素计算+!
    quicklist->head->count++;
    //返回是否创建新节点进行的插入元素
    return (orig_head != quicklist->head);
}

/* Add new entry to tail node of quicklist.
 *
 * Returns 0 if used existing tail.
 * Returns 1 if new tail created. */
//将value插入到quicklist的最后面的节点中，如果最后的节点不能插入，则创建一个新的ziplist类型的节点，插入到新的ziplist，并将ziplist插入到quicklist的尾部
//如果创建的新节点插入则返回1，否则返回0
int quicklistPushTail(quicklist *quicklist, void *value, size_t sz) {
    quicklistNode *orig_tail = quicklist->tail;
    //与上一个方法相同作用
    if (unlikely(isLargeElement(sz))) {
        __quicklistInsertPlainNode(quicklist, quicklist->tail, value, sz, 1);
        return 1;
    }
    //如果尾节点是ziplist并且有空间插入，则插入到尾节点的eof结束符之前，也就是尾部
    if (likely(
            _quicklistNodeAllowInsert(quicklist->tail, quicklist->fill, sz))) {
        quicklist->tail->entry = lpAppend(quicklist->tail->entry, value, sz);
        quicklistNodeUpdateSz(quicklist->tail);
    } else {
        //创建节点插入
        quicklistNode *node = quicklistCreateNode();
        node->entry = lpAppend(lpNew(0), value, sz);

        quicklistNodeUpdateSz(node);
        _quicklistInsertNodeAfter(quicklist, quicklist->tail, node);
    }
    quicklist->count++;
    quicklist->tail->count++;
    return (orig_tail != quicklist->tail);
}

/* Create new node consisting of a pre-formed listpack.
 * Used for loading RDBs where entire listpacks have been stored
 * to be retrieved later. */
//根据zl创建一个普通节点，并将创建的节点插入到最后面,zl是listpack
void quicklistAppendListpack(quicklist *quicklist, unsigned char *zl) {
    quicklistNode *node = quicklistCreateNode();

    node->entry = zl;
    node->count = lpLength(node->entry);
    node->sz = lpBytes(zl);

    _quicklistInsertNodeAfter(quicklist, quicklist->tail, node);
    quicklist->count += node->count;
}

/* Create new node consisting of a pre-formed plain node.
 * Used for loading RDBs where entire plain node has been stored
 * to be retrieved later.
 * data - the data to add (pointer becomes the responsibility of quicklist) */
//创建一个普通节点，将data放入节点，追加quicklist的最后面
void quicklistAppendPlainNode(quicklist *quicklist, unsigned char *data, size_t sz) {
    quicklistNode *node = quicklistCreateNode();

    node->entry = data;
    node->count = 1;
    node->sz = sz;
    node->container = QUICKLIST_NODE_CONTAINER_PLAIN;

    _quicklistInsertNodeAfter(quicklist, quicklist->tail, node);
    quicklist->count += node->count;
}

//n如果没有元素，则删除
#define quicklistDeleteIfEmpty(ql, n)                                          \
    do {                                                                       \
        if ((n)->count == 0) {                                                 \
            __quicklistDelNode((ql), (n));                                     \
            (n) = NULL;                                                        \
        }                                                                      \
    } while (0)

    //删除quicklist中的node节点，并释放node空间，如果删除node导致非压缩区域减小，则需要解压节点
REDIS_STATIC void __quicklistDelNode(quicklist *quicklist,
                                     quicklistNode *node) {
    /* Update the bookmark if any */
    //根据node查找是否存在指向他的书签
    quicklistBookmark *bm = _quicklistBookmarkFindByNode(quicklist, node);
    if (bm) {
        //将书签指向要删除节点的下一个
        bm->node = node->next;
        /* if the bookmark was to the last node, delete it. */
        //如果下一个接地那为NULL，则删除当前书签
        if (!bm->node)
            //删除节点的时候也要清除当前节点的书签，此函数就是做这个事
            _quicklistBookmarkDelete(quicklist, bm);
    }
    //将node前后节点相连
    if (node->next)
        node->next->prev = node->prev;
    if (node->prev)
        node->prev->next = node->next;
    //如果为头尾节点，还需要更新ql的头尾节点
    if (node == quicklist->tail) {
        quicklist->tail = node->prev;
    }

    if (node == quicklist->head) {
        quicklist->head = node->next;
    }

    /* Update len first, so in __quicklistCompress we know exactly len */
    //节点数-1
    quicklist->len--;
    //ql元素个数-节点元素个数
    quicklist->count -= node->count;

    /* If we deleted a node within our compress depth, we
     * now have compressed nodes needing to be decompressed. */
    //如果删除的是非压缩区域的节点，则需要将新进入非压缩区域的节点解压
    __quicklistCompress(quicklist, NULL);
    //释放lq
    zfree(node->entry);
    //释放qln
    zfree(node);
}

/* Delete one entry from list given the node for the entry and a pointer
 * to the entry in the node.
 *
 * Note: quicklistDelIndex() *requires* uncompressed nodes because you
 *       already had to get *p from an uncompressed node somewhere.
 *
 * Returns 1 if the entire node was deleted, 0 if node still exists.
 * Also updates in/out param 'p' with the next offset in the listpack. */
//删除ql中的p指向的元素，如果删除元素后，所在节点没有元素，则删除节点
REDIS_STATIC int quicklistDelIndex(quicklist *quicklist, quicklistNode *node,
                                   unsigned char **p) {
    int gone = 0;
    //不太可能是普通节点，如果是，直接删除node
    if (unlikely(QL_NODE_IS_PLAIN(node))) {
        __quicklistDelNode(quicklist, node);
        return 1;
    }
    //删除p指向的元素，并将p下一个元素的地址赋值给p
    node->entry = lpDelete(node->entry, *p, p);
    //元素-1
    node->count--;
    //如果node已经没有元素则删除node
    if (node->count == 0) {
        gone = 1;
        __quicklistDelNode(quicklist, node);
    } else {
        //更新qln的sz大小
        quicklistNodeUpdateSz(node);
    }
    //ql元素-1
    quicklist->count--;
    /* If we deleted the node, the original node is no longer valid */
    //如果删除了node则返回1
    return gone ? 1 : 0;
}

/* Delete one element represented by 'entry'
 *
 * 'entry' stores enough metadata to delete the proper position in
 * the correct listpack in the correct quicklist node. */
//删除一个由“entry”表示的元素“，更新迭代器当前指向的节点
void quicklistDelEntry(quicklistIter *iter, quicklistEntry *entry) {
    quicklistNode *prev = entry->node->prev;
    quicklistNode *next = entry->node->next;
    //删除entry指向的元素，如果删除了节点则deleted_node则为1
    int deleted_node = quicklistDelIndex((quicklist *)entry->quicklist,
                                         entry->node, &entry->zi);

    /* after delete, the zi is now invalid for any future usage. */
    //删除元素后，迭代器中的元素数据指向不再有用
    iter->zi = NULL;

    /* If current node is deleted, we must update iterator node and offset. */
    //如果发生节点删除，则需要更新迭代器当前节点的指向
    if (deleted_node) {
        //判断迭代器的迭代方向,然后根据方向，将current指向下一个元素
        if (iter->direction == AL_START_HEAD) {
            iter->current = next;
            iter->offset = 0;
        } else if (iter->direction == AL_START_TAIL) {
            iter->current = prev;
            iter->offset = -1;
        }
    }
    /* else if (!deleted_node), no changes needed.
     * we already reset iter->zi above, and the existing iter->offset
     * doesn't move again because:
     *   - [1, 2, 3] => delete offset 1 => [1, 3]: next element still offset 1
     *   - [1, 2, 3] => delete offset 0 => [2, 3]: next element still offset 0
     *  if we deleted the last element at offset N and now
     *  length of this listpack is N-1, the next call into
     *  quicklistNext() will jump to the next node. */
}

/* Replace quicklist entry by 'data' with length 'sz'. */
//将entry指向的元素换为长度为“sz”的“data”
//存在几个场景
//1.entry->node不是普通节点，替换元素不是大元素，则直接替换内容
//2.如果entry->node是普通节点,替换节点是大元素,不能直接替换zl节点中的元素，释放entry->node->entry，创建新的元素空间，并将替换元素数据拷贝进去
//3.entry->node是普通节点，但替换元素不是大元素，创建zl类型qln插入到entry->node附近，然后删除entry->node
//4.entry->node不是普通节点，替换元素是是大元素,根据data创建一个新qln，插入到entry指向的条目所在的node之后,删除因大元素插入分裂的后节点的尾部即entry->元素
void quicklistReplaceEntry(quicklistIter *iter, quicklistEntry *entry,
                           void *data, size_t sz)
{
    //获取条目所在的ql
    quicklist* quicklist = iter->quicklist;
    //很大可能entry->node不是普通节点，替换元素不是大元素，则直接替换内容
    if (likely(!QL_NODE_IS_PLAIN(entry->node) && !isLargeElement(sz))) {
        //将data替换到entry指向的元素位置
        entry->node->entry = lpReplace(entry->node->entry, &entry->zi, data, sz);
        //更新node的元素空间大小
        quicklistNodeUpdateSz(entry->node);
        /* quicklistNext() and quicklistGetIteratorEntryAtIdx() provide an uncompressed node */
        //压缩node，
        quicklistCompress(quicklist, entry->node);
    } else if (QL_NODE_IS_PLAIN(entry->node)) {
        //如果entry->node是普通节点,替换节点是大元素,不能直接替换zl节点中的元素，释放entry->node->entry，创建新的元素空间，并将替换元素数据拷贝进去
        if (isLargeElement(sz)) {
            //释放entry->node->entry的空间
            zfree(entry->node->entry);
            //重新分配替换元素大小的空间
            entry->node->entry = zmalloc(sz);
            //更新sz
            entry->node->sz = sz;
            //将替换内容拷贝到新的空间
            memcpy(entry->node->entry, data, sz);
            //执行压缩
            quicklistCompress(quicklist, entry->node);
        } else {
            //entry->node是普通节点，但替换元素不是大元素，创建zl类型qln插入到entry->node附近，然后删除entry->node
            //根据data创建一个新qln，插入到entry指向的条目所在的node之后
            quicklistInsertAfter(iter, entry, data, sz);
            //删除quicklist中的node节点，如果删除node导致非压缩区域减小，则需要解压节点
            __quicklistDelNode(quicklist, entry->node);
        }
    } else {
        //entry->node不是普通节点，替换元素是是大元素
        //根据data创建一个新qln，插入到entry指向的条目所在的node之后
        quicklistInsertAfter(iter, entry, data, sz);
        //如果entry->node只有一个元素直接删除掉完事
        if (entry->node->count == 1) {
            __quicklistDelNode(quicklist, entry->node);
        } else {
            //entyr->node不止一个元素，
            //获取entry指向的节点的最后一个元素，为什么取最后一个，因为entry->node不是普通节点，
            // 而且替换元素是大元素，则会在替换位置拆开2个qln，然后将大元素追加到后面，
            // 这样只需要删除entry->node的最后一个元素即是entyr->元素，quicklistInsertAfter
            unsigned char *p = lpSeek(entry->node->entry, -1);
            //删除最后一个元素
            quicklistDelIndex(quicklist, entry->node, &p);
            //压缩
            quicklistCompress(quicklist, entry->node->next);
        }
    }

    /* In any case, we reset iterator to forbid use of iterator after insert.
     * Notice: iter->current has been compressed above. */
    //重置迭代器
    resetIterator(iter);
}

/* Replace quicklist entry at offset 'index' by 'data' with length 'sz'.
 *
 * Returns 1 if replace happened.
 * Returns 0 if replace failed and no changes happened. */
//将ql的index位置的元素数据替换为data,成功返回1
int quicklistReplaceAtIndex(quicklist *quicklist, long index, void *data,
                            size_t sz) {
    quicklistEntry entry;
    //获取index位置的迭代器指向，如果idex为负数，offset也为元素所在节点的负数偏移量,并且entry也是index位置元素的包装对象
    quicklistIter *iter = quicklistGetIteratorEntryAtIdx(quicklist, index, &entry);
    if (likely(iter)) {
        //将entry指向的元素数据替换为data数据
        quicklistReplaceEntry(iter, &entry, data, sz);
        //释放迭代器
        quicklistReleaseIterator(iter);
        return 1;
    } else {
        return 0;
    }
}

/* Given two nodes, try to merge their listpacks.
 *
 * This helps us not have a quicklist with 3 element listpacks if
 * our fill factor can handle much higher levels.
 *
 * Note: 'a' must be to the LEFT of 'b'.
 *
 * After calling this function, both 'a' and 'b' should be considered
 * unusable.  The return value from this function must be used
 * instead of re-using any of the quicklistNode input arguments.
 *
 * Returns the input node picked to merge against or NULL if
 * merging was not possible. */
//合并a和b节点,合并后返回合并的新节点指针，合并失败返回NULL
REDIS_STATIC quicklistNode *_quicklistListpackMerge(quicklist *quicklist,
                                                    quicklistNode *a,
                                                    quicklistNode *b) {
    D("Requested merge (a,b) (%u, %u)", a->count, b->count);
    //解压a
    quicklistDecompressNode(a);
    //解压b
    quicklistDecompressNode(b);
    //合并a和b，合并失败则进入else，合并后，a或者b有一个为NULL
    if ((lpMerge(&a->entry, &b->entry))) {
        /* We merged listpacks! Now remove the unused quicklistNode. */
        //找到为NULL的节点，释放那个节点
        quicklistNode *keep = NULL, *nokeep = NULL;
        if (!a->entry) {
            nokeep = a;
            keep = b;
        } else if (!b->entry) {
            nokeep = b;
            keep = a;
        }
        //更新合并后节点的元素个数
        keep->count = lpLength(keep->entry);
        quicklistNodeUpdateSz(keep);

        //删除因合并后无效的节点，a和b的其中一个
        nokeep->count = 0;
        __quicklistDelNode(quicklist, nokeep);
        //压缩合并后的新节点
        quicklistCompress(quicklist, keep);
        return keep;
    } else {
        /* else, the merge returned NULL and nothing changed. */
        return NULL;
    }
}

/* Attempt to merge listpacks within two nodes on either side of 'center'.
 *
 * We attempt to merge:
 *   - (center->prev->prev, center->prev)
 *   - (center->next, center->next->next)
 *   - (center->prev, center)
 *   - (center, center->next)
 */
//尝试合并centre附近的节点，会做下面的合并尝试
//1.将center的前一个和前两个节点合并
//2.将center的后一个和后两个节点合并
//3.将center和前一个节点合并
//4.将center和后一个节点合并
REDIS_STATIC void _quicklistMergeNodes(quicklist *quicklist,
                                       quicklistNode *center) {

    int fill = quicklist->fill;
    quicklistNode *prev, *prev_prev, *next, *next_next, *target;
    prev = prev_prev = next = next_next = target = NULL;

    if (center->prev) {
        //初始化prev=center->prev
        //初始化prev_prev = center->prev->prev;
        prev = center->prev;
        if (center->prev->prev)
            prev_prev = center->prev->prev;
    }

    if (center->next) {
        //初始化next = center->next;
        //初始化next_next = center->next->next
        next = center->next;
        if (center->next->next)
            next_next = center->next->next;
    }

    /* Try to merge prev_prev and prev */
    //判断center的前一个节点和前两节点是否能合并，合并必须满足都是ziplist，并且合并后的大小小于等于fill对应的空间限制
    if (_quicklistNodeAllowMerge(prev, prev_prev, fill)) {
        //合并center前一个和前二个节点
        _quicklistListpackMerge(quicklist, prev_prev, prev);
        prev_prev = prev = NULL; /* they could have moved, invalidate them. */
    }

    /* Try to merge next and next_next */
    //判断center的后一个节点和后两节点是否能合并，合并必须满足都是ziplist，并且合并后的大小小于等于fill对应的空间限制
    if (_quicklistNodeAllowMerge(next, next_next, fill)) {
        _quicklistListpackMerge(quicklist, next, next_next);
        next = next_next = NULL; /* they could have moved, invalidate them. */
    }

    /* Try to merge center node and previous node */
    //判断center和他前一个节点是否能合并，合并必须满足都是ziplist，并且合并后的大小小于等于fill对应的空间限制
    if (_quicklistNodeAllowMerge(center, center->prev, fill)) {
        target = _quicklistListpackMerge(quicklist, center->prev, center);
        center = NULL; /* center could have been deleted, invalidate it. */
    } else {
        /* else, we didn't merge here, but target needs to be valid below. */
        target = center;
    }

    /* Use result of center merge (or original) to merge with next node. */
    //判断center和他后一个节点是否能合并，合并必须满足都是ziplist，并且合并后的大小小于等于fill对应的空间限制
    //为什么是target是因为，如果上面的合并成功，则center就失效了
    if (_quicklistNodeAllowMerge(target, target->next, fill)) {
        _quicklistListpackMerge(quicklist, target, target->next);
    }
}

/* Split 'node' into two parts, parameterized by 'offset' and 'after'.
 *
 * The 'after' argument controls which quicklistNode gets returned.
 * If 'after'==1, returned node has elements after 'offset'.
 *                input node keeps elements up to 'offset', including 'offset'.
 * If 'after'==0, returned node has elements up to 'offset'.
 *                input node keeps elements after 'offset', including 'offset'.
 *
 * Or in other words:
 * If 'after'==1, returned node will have elements after 'offset'.
 *                The returned node will have elements [OFFSET+1, END].
 *                The input node keeps elements [0, OFFSET].
 * If 'after'==0, returned node will keep elements up to but not including 'offset'.
 *                The returned node will have elements [0, OFFSET-1].
 *                The input node keeps elements [OFFSET, END].
 *
 * The input node keeps all elements not taken by the returned node.
 *
 * Returns newly created node or NULL if split not possible. */
//将node拆分2部分，按照offst为界限，如果after=1，则从node中移除offset+1到EOF的元素并返回，如果after=1则移除从0到offset-1的元素并返回
REDIS_STATIC quicklistNode *_quicklistSplitNode(quicklistNode *node, int offset,
                                                int after) {
    size_t zl_sz = node->sz;
    //创建一个新的qln
    quicklistNode *new_node = quicklistCreateNode();
    new_node->entry = zmalloc(zl_sz);

    /* Copy original listpack so we can split it */
    //将原来的node元素数据拷贝到新节点中
    memcpy(new_node->entry, node->entry, zl_sz);

    /* Ranges to be trimmed: -1 here means "continue deleting until the list ends" */
    //
    int orig_start = after ? offset + 1 : 0;
    int orig_extent = after ? -1 : offset;
    int new_start = after ? 0 : offset;
    int new_extent = after ? offset + 1 : -1;

    D("After %d (%d); ranges: [%d, %d], [%d, %d]", after, offset, orig_start,
      orig_extent, new_start, new_extent);

    node->entry = lpDeleteRange(node->entry, orig_start, orig_extent);
    node->count = lpLength(node->entry);
    quicklistNodeUpdateSz(node);

    new_node->entry = lpDeleteRange(new_node->entry, new_start, new_extent);
    new_node->count = lpLength(new_node->entry);
    quicklistNodeUpdateSz(new_node);

    D("After split lengths: orig (%d), new (%d)", node->count, new_node->count);
    return new_node;
}

/* Insert a new entry before or after existing entry 'entry'.
 *
 * If after==1, the new value is inserted after 'entry', otherwise
 * the new value is inserted before 'entry'. */
//将value插入到entry指向的元素附近，根据after决定插入方向
//插入会遇到比较多的场景，下面列举场景和解决方法
//1.entry指向的节点为NULL，看插入元素是否是大元素，是，则创建不同节点插入到ql的头尾，不是，则创建zl节点插入到ql头尾
//2.插入元素为大元素，如果entry->node是普通节点或者entry->元素在节点头部，插入元素也是头插入，或则entry->元素在尾部，插入元素也是为插入，则根据value创建普通节点插入到entry->node附近
//3.插入元素为大元素，entry->node不是普通节点也不满足entry->元素在节点头部，插入元素也是头插入，和entry->元素在尾部，插入元素也是为插入的情况，则拆分entry->node，根据after方向拆分，
// 拿到entry->元素之前或者之后的新的qln，将插入元素创建普通节点插入到新的qln头或者尾，再将新的qln插入到entry->node的头或者尾，
//4.插入元素不是大元素，entry->node可以插入元素，解压entry->node，插入到entry->元素附近，再压缩entry->node
//5.插入元素不是大元素，entry->node不能插入元素，但插入方向的最近节点可以插入，例如头插入，entry->node的上一个节点可以插入，则直接插入到entry->node上一个节点的尾部，尾插入则相反
//6.插入元素不是大元素，entry->node不能插入，插入方向最近的节点也不能插入，则拆分entry->node得到插入方向上的新qln，将插入元素插入到新的qln头或尾，将qln插入到entry->node头或尾，再以entry->node为中心尝试合并附近的节点
REDIS_STATIC void _quicklistInsert(quicklistIter *iter, quicklistEntry *entry,
                                   void *value, const size_t sz, int after)
{
    quicklist *quicklist = iter->quicklist;
    int full = 0, at_tail = 0, at_head = 0, avail_next = 0, avail_prev = 0;
    int fill = quicklist->fill;
    //获取元素所在节点
    quicklistNode *node = entry->node;
    quicklistNode *new_node = NULL;
    //如果entry指向的节点是空的
    if (!node) {
        /* we have no reference node, so let's create only node in the list */
        D("No node given!");
        //插入的元素不太可能是大元素
        if (unlikely(isLargeElement(sz))) {
            //如果是大元素,则根据value创建qln插入到ql的尾结点附近，after决定前后
            __quicklistInsertPlainNode(quicklist, quicklist->tail, value, sz, after);
            return;
        }
        //插入的元素不是大元素，则创建节点，插入到ql中
        new_node = quicklistCreateNode();
        new_node->entry = lpPrepend(lpNew(0), value, sz);
        __quicklistInsertNode(quicklist, NULL, new_node, after);
        new_node->count++;
        quicklist->count++;
        return;
    }

    /* Populate accounting flags for easier boolean checks later */
    //判断节点是否能插入，不能插入则full=1
    if (!_quicklistNodeAllowInsert(node, fill, sz)) {
        D("Current node is full with count %d with requested fill %d",
          node->count, fill);
        full = 1;
    }
    //判断entry指向的条目是不是在当前节点的最末尾，是则at_tail=1
    if (after && (entry->offset == node->count - 1 || entry->offset == -1)) {
        D("At Tail of current listpack");
        at_tail = 1;
        //判断entry指向的节点的下一个节点是否可以插入,可以则avail_next=1
        if (_quicklistNodeAllowInsert(node->next, fill, sz)) {
            D("Next node is available.");
            avail_next = 1;
        }
    }
    //判断entry指向的条目是不是在当前节点的首位，是则at_head=1
    if (!after && (entry->offset == 0 || entry->offset == -(node->count))) {
        D("At Head");
        at_head = 1;
        //判断entry指向的节点的前一个节点是否可以插入,可以则avail_prev=1
        if (_quicklistNodeAllowInsert(node->prev, fill, sz)) {
            D("Prev node is available.");
            avail_prev = 1;
        }
    }
    //插入元素不太可能是大元素
    if (unlikely(isLargeElement(sz))) {
        //如果是普通节点，或者满足头插入，则插入头，满足尾插则插入尾，创建普通节点插入
        if (QL_NODE_IS_PLAIN(node) || (at_tail && after) || (at_head && !after)) {
            __quicklistInsertPlainNode(quicklist, node, value, sz, after);
        } else {
            //entry->node不是普通节点，entry->元素和插入元素也不是节点尾部尾插，节点头部头插，先解压当前节点,将重压缩设为1
            quicklistDecompressNodeForUse(node);
            //拆分node，根据after得到offset之前的元素集合节点后者之后的元素集合节点
            new_node = _quicklistSplitNode(node, entry->offset, after);
            quicklistNode *entry_node = __quicklistCreatePlainNode(value, sz);
            //在将新节点插入到拆分后的节点附近，完成插入
            __quicklistInsertNode(quicklist, node, entry_node, after);
            __quicklistInsertNode(quicklist, entry_node, new_node, after);
            quicklist->count++;
        }
        return;
    }

    /* Now determine where and how to insert the new element */
    //full表示当前节点不能插入!full=true表示能插入
    if (!full && after) {
        D("Not full, inserting after current position.");
        //解压缩当前节点，并设置重压缩等于1
        quicklistDecompressNodeForUse(node);
        //插入到entry指向的元素之后
        node->entry = lpInsertString(node->entry, value, sz, entry->zi, LP_AFTER, NULL);
        node->count++;
        quicklistNodeUpdateSz(node);
        //重压缩
        quicklistRecompressOnly(node);
    } else if (!full && !after) {
        D("Not full, inserting before current position.");
        //当前节点能插入，插入到entry指向的元素前
        //解压缩，设置重压缩=1
        quicklistDecompressNodeForUse(node);
        //插入到entry指向的元素之前
        node->entry = lpInsertString(node->entry, value, sz, entry->zi, LP_BEFORE, NULL);
        node->count++;
        quicklistNodeUpdateSz(node);
        //重压缩
        quicklistRecompressOnly(node);
    } else if (full && at_tail && avail_next && after) {
        //当前节点不能插入，但当entry指向的元素在尾部，entry指向的节点下一个节点可以插入，并且是新元素是尾插入
        /* If we are: at tail, next has free space, and inserting after:
         *   - insert entry at head of next node. */
        D("Full and tail, but next isn't full; inserting next node head");
        //获取到当前的下一个节点
        new_node = node->next;
        //解压缩，设置重压缩=1
        quicklistDecompressNodeForUse(new_node);
        //插入到下一个节点的头部
        new_node->entry = lpPrepend(new_node->entry, value, sz);
        new_node->count++;
        quicklistNodeUpdateSz(new_node);
        quicklistRecompressOnly(new_node);
        quicklistRecompressOnly(node);
    } else if (full && at_head && avail_prev && !after) {
        //当前节点不能插入，但当entry指向的元素在头部，entry指向的节点上一个节点可以插入，并且是新元素是头插入
        /* If we are: at head, previous has free space, and inserting before:
         *   - insert entry at tail of previous node. */
        D("Full and head, but prev isn't full, inserting prev node tail");
        //获取上一个节点
        new_node = node->prev;
        quicklistDecompressNodeForUse(new_node);
        //插入到上一个节点的尾部
        new_node->entry = lpAppend(new_node->entry, value, sz);
        new_node->count++;
        quicklistNodeUpdateSz(new_node);
        quicklistRecompressOnly(new_node);
        quicklistRecompressOnly(node);
    } else if (full && ((at_tail && !avail_next && after) ||
                        (at_head && !avail_prev && !after))) {
        //当前节点不能插入，同时也不满足节点附近节点插入情况
        /* If we are: full, and our prev/next has no available space, then:
         *   - create new node and attach to quicklist */
        D("\tprovisioning new node...");
        //创建一个qln
        new_node = quicklistCreateNode();
        //创建zl，赋值到qln
        new_node->entry = lpPrepend(lpNew(0), value, sz);
        new_node->count++;
        quicklistNodeUpdateSz(new_node);
        //将新建的qln插入到entry指向的node附近
        __quicklistInsertNode(quicklist, node, new_node, after);
    } else if (full) {
        //当entry指向的节点是满的，并且不是entry指向的元素不再节点的头尾，则只能拆分entry指向的节点
        /* else, node is full we need to split it. */
        /* covers both after and !after cases */
        D("\tsplitting node...");
        //解压缩entry->node
        quicklistDecompressNodeForUse(node);
        //拆分entry->node，得到向前后者向后的新的qln
        new_node = _quicklistSplitNode(node, entry->offset, after);
        if (after)
            //将插入元素插入到offset+1的头部，就是插入到了entry指向的元素的尾部，即offset+1的位置
            new_node->entry = lpPrepend(new_node->entry, value, sz);
        else
            //将插入元素插入到offset-1的尾部，就是插入到了entry指向的元素的头部，即offset-1的位置
            new_node->entry = lpAppend(new_node->entry, value, sz);
        new_node->count++;
        quicklistNodeUpdateSz(new_node);
        //将新建节点追加到node附近
        __quicklistInsertNode(quicklist, node, new_node, after);
        //尝试合并entry->node附近的节点
        _quicklistMergeNodes(quicklist, node);
    }

    quicklist->count++;

    /* In any case, we reset iterator to forbid use of iterator after insert.
     * Notice: iter->current has been compressed in _quicklistInsert(). */
    //重置迭代器
    resetIterator(iter); 
}

//将value元素插入到entry指向的元素前面，可能发生节点分裂和合并，详细场景见此方法调用的方法
void quicklistInsertBefore(quicklistIter *iter, quicklistEntry *entry,
                           void *value, const size_t sz)
{
    _quicklistInsert(iter, entry, value, sz, 0);
}

//将value元素插入到entry指向的元素后面，可能发生节点分裂和合并，详细场景见此方法调用的方法
void quicklistInsertAfter(quicklistIter *iter, quicklistEntry *entry,
                          void *value, const size_t sz)
{
    _quicklistInsert(iter, entry, value, sz, 1);
}

/* Delete a range of elements from the quicklist.
 *
 * elements may span across multiple quicklistNodes, so we
 * have to be careful about tracking where we start and end.
 *
 * Returns 1 if entries were deleted, 0 if nothing was deleted. */
//从快速列表中删除一系列元素。元素可能跨越多个QuickListNode，
//因此我们必须小心跟踪起点和终点。如果条目已删除，则返回1；如果未删除任何内容，则返回0。
//如果某个节点所有元素都被删除了，那么节点也会被删除
int quicklistDelRange(quicklist *quicklist, const long start,
                      const long count) {
    //非正常参数结束函数
    if (count <= 0)
        return 0;
    //删除的元素个数
    unsigned long extent = count; /* range is inclusive of start position */
    //判断count是不是超出列表范围，是设置结束位置为最后一个元素位置
    if (start >= 0 && extent > (quicklist->count - start)) {
        /* if requesting delete more elements than exist, limit to list size. */
        extent = quicklist->count - start;
    } else if (start < 0 && extent > (unsigned long)(-start)) {
        /* else, if at negative offset, limit max size to rest of list. */
        //-start表示从头方向，从start开始后面剩余多少个元素，如果extent即count大于-start则超出范围，将extent设置为取到最尾节点的位置
        extent = -start; /* c.f. LREM -29 29; just delete until end. */
    }
    //找到start元素包装为iter,方向为从尾开始
    quicklistIter *iter = quicklistGetIteratorAtIdx(quicklist, AL_START_TAIL, start);
    if (!iter)
        return 0;

    D("Quicklist delete request for start %ld, count %ld, extent: %ld", start,
      count, extent);
    //获取start指向元素所在的节点和元素偏移量
    quicklistNode *node = iter->current;
    long offset = iter->offset;
    //释放iter
    quicklistReleaseIterator(iter);

    /* iterate over next nodes until everything is deleted. */
    //extent是需要删除的元素个数，每次遍历都是再遍历节点中删除元素，当删除元素时，extent会=extent-删除的元素个数
    while (extent) {
        //node初始为iter->current，获取iter的下一个节点,作为循环条件
        quicklistNode *next = node->next;

        unsigned long del;
        int delete_entire_node = 0;
        //此if else语句，主要获取当前遍历节点中，需要删除的元素个数
        //如果开始元素是节点的首元素，并且取元素的范围大于等于开始节点的元素个数，
        // 则表示开始节点所有元素都在删除范围内，直接设置delete_entire_node=1，表示此节点需要删除
        if (offset == 0 && extent >= node->count) {
            /* If we are deleting more than the count of this node, we
             * can just delete the entire node without listpack math. */
            delete_entire_node = 1;
            del = node->count;
        } else if (offset >= 0 && extent + offset >= node->count) {
            /* If deleting more nodes after this one, calculate delete based
             * on size of current node. */
            del = node->count - offset;
        } else if (offset < 0) {
            /* If offset is negative, we are in the first run of this loop
             * and we are deleting the entire range
             * from this start offset to end of list.  Since the Negative
             * offset is the number of elements until the tail of the list,
             * just use it directly as the deletion count. */
            del = -offset;

            /* If the positive offset is greater than the remaining extent,
             * we only delete the remaining extent, not the entire offset.
             */
            if (del > extent)
                del = extent;
        } else {
            /* else, we are deleting less than the extent of this node, so
             * use extent directly. */
            del = extent;
        }

        D("[%ld]: asking to del: %ld because offset: %d; (ENTIRE NODE: %d), "
          "node count: %u",
          extent, del, offset, delete_entire_node, node->count);
        //如果当前遍历节点所有元素都在删除范围，或者当前节点是普通节点，则删除当前节点，为什么普通节点直接删除，是因为extent大于0才能进入循环，所以不存在删除0个长度的元素
        if (delete_entire_node || QL_NODE_IS_PLAIN(node)) {
            __quicklistDelNode(quicklist, node);
        } else {
            //如果不能直接删除节点，则解压缩当前节点，删除从offset开始到此节点要删除的元素个数del
            //解压缩
            quicklistDecompressNodeForUse(node);
            //删除当前节点需要删除的元素
            node->entry = lpDeleteRange(node->entry, offset, del);
            //更新node-sz
            quicklistNodeUpdateSz(node);
            //节点元素个数-删除个数
            node->count -= del;
            //ql列表元素个数-删除个数
            quicklist->count -= del;
            //如果删除元素后，遍历的当前节点没有元素，则删除当前遍历的节点
            quicklistDeleteIfEmpty(quicklist, node);
            if (node)
                //重压缩
                quicklistRecompressOnly(node);
        }
        //更新还需删除的元素个数
        extent -= del;
        //遍历条件变量，指下一个节点
        node = next;
        //下个节点从头开始删除
        offset = 0;
    }
    return 1;
}

/* compare between a two entries */
//将entry指向的元素和p2指向的元素进行比较，p2_len为p2指向的元素长度
//相等则返回1
int quicklistCompare(quicklistEntry* entry, unsigned char *p2, const size_t p2_len) {
    //不太可能是普通节点
    if (unlikely(QL_NODE_IS_PLAIN(entry->node))) {
        return ((entry->sz == p2_len) && (memcmp(entry->value, p2, p2_len) == 0));
    }
    return lpCompare(entry->zi, p2, p2_len);
}

/* Returns a quicklist iterator 'iter'. After the initialization every
 * call to quicklistNext() will return the next element of the quicklist. */
//创建化迭代器，directio来确定迭代方向
quicklistIter *quicklistGetIterator(quicklist *quicklist, int direction) {
    quicklistIter *iter;
    //分配qli空间
    iter = zmalloc(sizeof(*iter));
    //初始化迭代器当前节点和元素偏移量
    if (direction == AL_START_HEAD) {
        iter->current = quicklist->head;
        iter->offset = 0;
    } else if (direction == AL_START_TAIL) {
        iter->current = quicklist->tail;
        iter->offset = -1;
    }
    //设置方向
    iter->direction = direction;
    iter->quicklist = quicklist;

    iter->zi = NULL;

    return iter;
}

/* Initialize an iterator at a specific offset 'idx' and make the iterator
 * return nodes in 'direction' direction. */
//找到idx位置的元素，并返回指向他的迭代器，迭代器设置为direction方向
//进行了过半优化，如果寻找方向上需要迭代半数以上的元素，则反转方向寻找
//如果idx<0则返回的quicklistIter也是当前元素所在节点的负数偏移量
quicklistIter *quicklistGetIteratorAtIdx(quicklist *quicklist,
                                         const int direction,
                                         const long long idx)
{
    //开始的节点
    quicklistNode *n;
    unsigned long long accum = 0;
    unsigned long long index;
    //如果大于0就从头到尾找，如果小于0则从尾到头找
    int forward = idx < 0 ? 0 : 1; /* < 0 -> reverse, 0+ -> forward */
    //如果是从头开始找，则idx就是从头到元素的偏移量，如果从尾开始找，则idx为负数，则取idx绝对值-1则是从尾到元素的偏移量
    index = forward ? idx : (-idx) - 1;
    if (index >= quicklist->count)
        return NULL;

    /* Seek in the other direction if that way is shorter. */
    int seek_forward = forward;
    unsigned long long seek_index = index;
    //如果寻找的方向上，需要偏移过半以上的元素才能找到idx位置的元素，则两级反转方向，节省遍历的元素
    if (index > (quicklist->count - 1) / 2) {
        //反转方向
        seek_forward = !forward;
        //反转后的偏移量=总元素-1-原来的偏移量
        seek_index = quicklist->count - 1 - index;
    }

    //如果是大于0就从头节点开始，小于0则从尾结点开始
    n = seek_forward ? quicklist->head : quicklist->tail;
    //寻找元素所在的节点
    while (likely(n)) {
        //当经过的节点元素和大于seek_index时，则说明寻找的元素在这个节点上
        if ((accum + n->count) > seek_index) {
            break;
        } else {
            D("Skipping over (%p) %u at accum %lld", (void *)n, n->count,
              accum);
            //指向下一个节点
            accum += n->count;
            n = seek_forward ? n->next : n->prev;
        }
    }
    //如果没找到元素所在的节点，返回NULL
    if (!n)
        return NULL;

    /* Fix accum so it looks like we seeked in the other direction. */
    //如果seek_forward!=forward则进行了优化反转了方向寻找，那么遍历经过的元素总数=总元素数-反方向经过的元素和-元素所在节点的元素和
    if (seek_forward != forward) accum = quicklist->count - n->count - accum;

    D("Found node: %p at accum %llu, idx %llu, sub+ %llu, sub- %llu", (void *)n,
      accum, index, index - accum, (-index) - 1 + accum);
    //初始化迭代器，direction指定方向
    quicklistIter *iter = quicklistGetIterator(quicklist, direction);
    //将迭代器，指向找到的节点
    iter->current = n;
    //计算当前元素在节点中的偏移量，如果是从头找则等于
    if (forward) {
        /* forward = normal head-to-tail offset. */
        iter->offset = index - accum;
    } else {
        /* reverse = need negative offset for tail-to-head, so undo
         * the result of the original index = (-idx) - 1 above. */
        //index为负数经过-index-1，还原回来也是-indxe-1，加上accum则当前元素在当前节点的负数偏移量
        iter->offset = (-index) - 1 + accum;
    }

    return iter;
}

/* Release iterator.
 * If we still have a valid current node, then re-encode current node. */
//释放迭代器。如果iter指向一个有效的当前节点，那么重新压缩当前节点。
void quicklistReleaseIterator(quicklistIter *iter) {
    if (!iter) return;
    if (iter->current)
        quicklistCompress(iter->quicklist, iter->current);

    zfree(iter);
}

/* Get next element in iterator.
 *
 * Note: You must NOT insert into the list while iterating over it.
 * You *may* delete from the list while iterating using the
 * quicklistDelEntry() function.
 * If you insert into the quicklist while iterating, you should
 * re-create the iterator after your addition.
 *
 * iter = quicklistGetIterator(quicklist,<direction>);
 * quicklistEntry entry;
 * while (quicklistNext(iter, &entry)) {
 *     if (entry.value)
 *          [[ use entry.value with entry.sz ]]
 *     else
 *          [[ use entry.longval ]]
 * }
 *
 * Populates 'entry' with values for this iteration.
 * Returns 0 when iteration is complete or if iteration not possible.
 * If return value is 0, the contents of 'entry' are not valid.
 */
//获取iter下一个元素，但是也有几种场景
//1.如果iter->zi为NULL，则可能是根据某个元素位置开始创建的迭代器，则获取iter->offset位置上的元素数据，如果没有获取到元素数据，则说明此节点已经完结，则获取下个节点的元素
//2.如果iter->zi不为NULL，则获取iter方向上的下一个元素
//获取到的元素会用entry包装
int quicklistNext(quicklistIter *iter, quicklistEntry *entry) {
    //初始化entry
    initEntry(entry);
    //非空判断
    if (!iter) {
        D("Returning because no iter!");
        return 0;
    }
    //设置qlt->node等于当前迭代器所在的节点
    entry->quicklist = iter->quicklist;
    entry->node = iter->current;
    //非空判断
    if (!iter->current) {
        D("Returning because current node is NULL");
        return 0;
    }

    unsigned char *(*nextFn)(unsigned char *, unsigned char *) = NULL;
    int offset_update = 0;

    int plain = QL_NODE_IS_PLAIN(iter->current);
    //如果iter没有指向元素的数据,则找到到iter->offset对应的元素数据
    if (!iter->zi) {
        /* If !zi, use current index. */
        //解压，设置重压缩
        quicklistDecompressNodeForUse(iter->current);
        //不太可能是普通节点，如果是普通节点，则直接设置iter->zi=节点的->entry
        if (unlikely(plain))
            iter->zi = iter->current->entry;
        else
            //获取iter->current->entry的offset位置元素数据
            iter->zi = lpSeek(iter->current->entry, iter->offset);
    } else if (unlikely(plain)) {
        //如果iter当前节点是普通节点，则当前元素数据为NULL
        iter->zi = NULL;
    } else {
        /* else, use existing iterator offset and get prev/next as necessary. */
        //如果iter指向的当前元素有数据，则根据迭代方向，获取下一个元素
        if (iter->direction == AL_START_HEAD) {
            nextFn = lpNext;
            offset_update = 1;
        } else if (iter->direction == AL_START_TAIL) {
            nextFn = lpPrev;
            offset_update = -1;
        }
        //获取iter->zi下一个元素
        iter->zi = nextFn(iter->current->entry, iter->zi);
        //更新迭代器
        iter->offset += offset_update;
    }
    //设置qle
    entry->zi = iter->zi;
    entry->offset = iter->offset;
    //iter->zi为不为NULL，则
    if (iter->zi) {
        //直接将普通节点的数据赋值给qlt
        if (unlikely(plain)) {
            entry->value = entry->node->entry;
            entry->sz = entry->node->sz;
            return 1;
        }
        /* Populate value from existing listpack position */
        unsigned int sz = 0;
        //获取entry指向的元素值
        entry->value = lpGetValue(entry->zi, &sz, &entry->longval);
        entry->sz = sz;
        return 1;
    } else {
        /* We ran out of listpack entries.
         * Pick next node, update offset, then re-run retrieval. */
        //如果iter->zi为NULL,则说明当前节点已经遍历完了
        //压缩当前节点
        quicklistCompress(iter->quicklist, iter->current);
        if (iter->direction == AL_START_HEAD) {
            /* Forward traversal */
            D("Jumping to start of next node");
            iter->current = iter->current->next;
            iter->offset = 0;
        } else if (iter->direction == AL_START_TAIL) {
            /* Reverse traversal */
            D("Jumping to end of previous node");
            iter->current = iter->current->prev;
            iter->offset = -1;
        }
        iter->zi = NULL;
        //获取下一个节点的同一方向上的第一个元素
        return quicklistNext(iter, entry);
    }
}

/* Sets the direction of a quicklist iterator. */
//设置iter迭代器的迭代方向,direction为新的迭代方向
void quicklistSetDirection(quicklistIter *iter, int direction) {
    iter->direction = direction;
}

/* Duplicate the quicklist.
 * On success a copy of the original quicklist is returned.
 *
 * The original quicklist both on success or error is never modified.
 *
 * Returns newly allocated quicklist. */
//复制快速列表。成功后，将返回原始快速列表的副本。无论成功与否，原始的快速列表都不会被修改。返回新分配的quicklist。
//工作原理:遍历orig中的每个qln，然后分配相同的空间，将数据拷贝到qln中
quicklist *quicklistDup(quicklist *orig) {
    quicklist *copy;
    //创建ql
    copy = quicklistNew(orig->fill, orig->compress);
    //遍历orig列表中的节点
    for (quicklistNode *current = orig->head; current;
         current = current->next) {
        //创建zl类型的qln
        quicklistNode *node = quicklistCreateNode();
        //将遍历节点的数据赋值到新的qln
        if (current->encoding == QUICKLIST_NODE_ENCODING_LZF) {
            //LZF类型的qln节点数据复制
            quicklistLZF *lzf = (quicklistLZF *)current->entry;
            //获取lzf的大小，lzf头+lp大小
            size_t lzf_sz = sizeof(*lzf) + lzf->sz;
            //分配相同大小的空间
            node->entry = zmalloc(lzf_sz);
            //将LZF的数据拷贝到新的qln->entry中
            memcpy(node->entry, current->entry, lzf_sz);
        } else if (current->encoding == QUICKLIST_NODE_ENCODING_RAW) {
            //如果是RAW编码，则直接分配相同空间，然后赋值到新的qln->entry中
            node->entry = zmalloc(current->sz);
            memcpy(node->entry, current->entry, current->sz);
        }
        //qln属性的拷贝
        node->count = current->count;
        copy->count += node->count;
        node->sz = current->sz;
        node->encoding = current->encoding;
        node->container = current->container;
        //将新的qln插入到新的ql的尾部
        _quicklistInsertNodeAfter(copy, copy->tail, node);
    }

    /* copy->count must equal orig->count here */
    return copy;
}

/* Populate 'entry' with the element at the specified zero-based index
 * where 0 is the head, 1 is the element next to head
 * and so on. Negative integers are used in order to count
 * from the tail, -1 is the last element, -2 the penultimate
 * and so on. If the index is out of range 0 is returned.
 *
 * Returns an iterator at a specific offset 'idx' if element found
 * Returns NULL if element not found */
//找到idx位置元素，并初始化迭代器，按照从尾向头的方向初始化迭代器，并将idx位置的元素用entry包装
quicklistIter *quicklistGetIteratorEntryAtIdx(quicklist *quicklist, const long long idx,
                                              quicklistEntry *entry)
{
    //从尾开始找idx位置的元素,用iter指向
    quicklistIter *iter = quicklistGetIteratorAtIdx(quicklist, AL_START_TAIL, idx);
    //如果idx没有元素返回NULL
    if (!iter) return NULL;
    //这里的iter是根据idx创建的，iter->zi为NULL，所以不会获取下一个元素，而是根据iter->zi获取到元素并放到qle中即entry中
    assert(quicklistNext(iter, entry));
    return iter;
}

//将尾节点提到头部，作为新的头节点,原来的头节点作为第二个节点，倒数第二个节点作为新的尾节点
static void quicklistRotatePlain(quicklist *quicklist) {
    //将尾节点作为新的头节点
    quicklistNode *new_head = quicklist->tail;
    //尾节点作为新的头节点，那么就拿倒数第二个节点作为新的尾节点
    quicklistNode *new_tail = quicklist->tail->prev;
    //将久的头节点的上一个节点指向新的头结点
    quicklist->head->prev = new_head;
    //将新的尾结点的下一个节点置为NULL
    new_tail->next = NULL;
    //将新的头节点的下一个节点指向久的头节点
    new_head->next = quicklist->head;
    //将新的头节点的上一个节点置为NULL
    new_head->prev = NULL;
    //将ql的头节点指向新的头节点
    quicklist->head = new_head;
    //将ql的尾节点指向新的尾节点
    quicklist->tail = new_tail;
}

/* Rotate quicklist by moving the tail element to the head. */
//将尾元素作为新的头元素
void quicklistRotate(quicklist *quicklist) {
    //如果只有一个元素则直接结束
    if (quicklist->count <= 1)
        return;

    //不太可能是普通节点,如果是普通元素，直接将尾节点提到头节点完事
    if (unlikely(QL_NODE_IS_PLAIN(quicklist->tail))) {
        quicklistRotatePlain(quicklist);
        return;
    }

    /* First, get the tail entry */
    //获取尾节点中的尾元素指针
    unsigned char *p = lpSeek(quicklist->tail->entry, -1);
    unsigned char *value, *tmp;
    long long longval;
    unsigned int sz;
    char longstr[32] = {0};
    //获取尾元素的值
    tmp = lpGetValue(p, &sz, &longval);

    /* If value found is NULL, then lpGet populated longval instead */
    //如果tmp为NULL则说明获取到的是整型值，为longval
    if (!tmp) {
        /* Write the longval as a string so we can re-add it */
        //将longval转为字符串
        sz = ll2string(longstr, sizeof(longstr), longval);
        value = (unsigned char *)longstr;
    } else if (quicklist->len == 1) {
        /* Copy buffer since there could be a memory overlap when move
         * entity from tail to head in the same listpack. */
        //进入这里，则表示获取到的是字符串,并且ql中只有一个节点，因为在同一个列表包中将实体从尾部移动到头部时，可能会有内存重叠。
        //则将字符串拷贝一份
        value = zmalloc(sz);
        memcpy(value, tmp, sz);
    } else {
        //不存在覆盖问题，直接将value=字符串地址
        value = tmp;
    }

    /* Add tail entry to head (must happen before tail is deleted). */
    //将尾元素插入到头部
    quicklistPushHead(quicklist, value, sz);

    /* If quicklist has only one node, the head listpack is also the
     * tail listpack and PushHead() could have reallocated our single listpack,
     * which would make our pre-existing 'p' unusable. */
    //如果ql只有一个节点，那么上面将尾元素值插入到头部后，原来指向尾元素的指针就失效了，所以重新获取一下
    if (quicklist->len == 1) {
        p = lpSeek(quicklist->tail->entry, -1);
    }

    /* Remove tail entry. */
    //移除尾元素
    quicklistDelIndex(quicklist, quicklist->tail, &p);
    //释放上面分配的内存
    if (value != (unsigned char*)longstr && value != tmp)
        zfree(value);
}

/* pop from quicklist and return result in 'data' ptr.  Value of 'data'
 * is the return value of 'saver' function pointer if the data is NOT a number.
 *
 * If the quicklist element is a long long, then the return value is returned in
 * 'sval'.
 *
 * Return value of 0 means no elements available.
 * Return value of 1 means check 'data' and 'sval' for values.
 * If 'data' is set, use 'data' and 'sz'.  Otherwise, use 'sval'. */
//从快速列表中弹出，并在“数据”ptr中返回结果。
// 如果数据不是数字，“data”的值是“saver”函数指针的返回值,即弹出元素的副本。
// 如果quicklist元素为long-long， 则返回值以“sval”形式返回。
// 返回值0表示没有可用的元素。
// 返回值1表示检查“data”和“sval”中的值。如果设置了“data”，则使用“data”和“sz”。否则，请使用“sval”。
int quicklistPopCustom(quicklist *quicklist, int where, unsigned char **data,
                       size_t *sz, long long *sval,
                       void *(*saver)(unsigned char *data, size_t sz)) {
    unsigned char *p;
    unsigned char *vstr;
    unsigned int vlen;
    long long vlong;
    //获取弹出的方向，如果where==0则从头部弹出，反之从尾部弹出
    int pos = (where == QUICKLIST_HEAD) ? 0 : -1;
    //如果没有元素,结束函数
    if (quicklist->count == 0)
        return 0;
    //将形参置为NULL
    if (data)
        *data = NULL;
    if (sz)
        *sz = 0;
    if (sval)
        *sval = -123456789;
    //将形参置为NULL
    //获取弹出元素所在的节点，如果头弹出则拿头节点，反之亦然
    quicklistNode *node;
    if (where == QUICKLIST_HEAD && quicklist->head) {
        node = quicklist->head;
    } else if (where == QUICKLIST_TAIL && quicklist->tail) {
        node = quicklist->tail;
    } else {
        return 0;
    }

    /* The head and tail should never be compressed */
    //头部和尾部永远不能被压缩
    assert(node->encoding != QUICKLIST_NODE_ENCODING_LZF);
    //不太可能是普通节点
    if (unlikely(QL_NODE_IS_PLAIN(node))) {
        //如果data不就是NULL，调用复制函数saver，生成副本数据并赋值给data
        if (data)
            *data = saver(node->entry, node->sz);
        if (sz)
            *sz = node->sz;
        //删除节点
        quicklistDelIndex(quicklist, node, NULL);
        return 1;
    }
    //获取头或者尾元素
    p = lpSeek(node->entry, pos);
    //获取元素值
    vstr = lpGetValue(p, &vlen, &vlong);
    if (vstr) {
        //如果data不就是NULL，调用复制函数saver，生成副本数据并赋值给data
        if (data)
            *data = saver(vstr, vlen);
        if (sz)
            *sz = vlen;
    } else {
        if (data)
            *data = NULL;
        if (sval)
            *sval = vlong;
    }
    //删除弹出元素
    quicklistDelIndex(quicklist, node, &p);
    return 1;
}

/* Return a malloc'd copy of data passed in */
//返回传入数据的malloc'd副本，用户qln元素弹出时的数据拷贝
REDIS_STATIC void *_quicklistSaver(unsigned char *data, size_t sz) {
    unsigned char *vstr;
    if (data) {
        vstr = zmalloc(sz);
        memcpy(vstr, data, sz);
        return vstr;
    }
    return NULL;
}

/* Default pop function
 *
 * Returns malloc'd value from quicklist */
//从ql中弹出元素
//where决定是头部还是尾部弹出
//弹出的元素值是字符串，则为data，sz为字符串长度
//弹出的元素值是数字，则为slong
int quicklistPop(quicklist *quicklist, int where, unsigned char **data,
                 size_t *sz, long long *slong) {
    unsigned char *vstr;
    size_t vlen;
    long long vlong;
    if (quicklist->count == 0)
        return 0;
    int ret = quicklistPopCustom(quicklist, where, &vstr, &vlen, &vlong,
                                 _quicklistSaver);
    if (data)
        *data = vstr;
    if (slong)
        *slong = vlong;
    if (sz)
        *sz = vlen;
    return ret;
}

/* Wrapper to allow argument-based switching between HEAD/TAIL pop */
//将value插入到ql中，sz是value的长度，where==0则插入到头，反之亦然
void quicklistPush(quicklist *quicklist, void *value, const size_t sz,
                   int where) {
    /* The head and tail should never be compressed (we don't attempt to decompress them) */
    //首尾永不压缩
    if (quicklist->head)
        assert(quicklist->head->encoding != QUICKLIST_NODE_ENCODING_LZF);
    if (quicklist->tail)
        assert(quicklist->tail->encoding != QUICKLIST_NODE_ENCODING_LZF);
    //头插入
    if (where == QUICKLIST_HEAD) {
        quicklistPushHead(quicklist, value, sz);
    } else if (where == QUICKLIST_TAIL) {
        //尾插入
        quicklistPushTail(quicklist, value, sz);
    }
}

/* Print info of quicklist which is used in debugCommand. */
//打印ql的信息,用于调试
void quicklistRepr(unsigned char *ql, int full) {
    int i = 0;
    quicklist *quicklist  = (struct quicklist*) ql;
    printf("{count : %ld}\n", quicklist->count);
    printf("{len : %ld}\n", quicklist->len);
    printf("{fill : %d}\n", quicklist->fill);
    printf("{compress : %d}\n", quicklist->compress);
    printf("{bookmark_count : %d}\n", quicklist->bookmark_count);
    quicklistNode* node = quicklist->head;

    while(node != NULL) {
        printf("{quicklist node(%d)\n", i++);
        printf("{container : %s, encoding: %s, size: %zu, recompress: %d, attempted_compress: %d}\n",
               QL_NODE_IS_PLAIN(node) ? "PLAIN": "PACKED",
               (node->encoding == QUICKLIST_NODE_ENCODING_RAW) ? "RAW": "LZF",
               node->sz,
               node->recompress,
               node->attempted_compress);

        if (full) {
            quicklistDecompressNode(node);
            if (node->container == QUICKLIST_NODE_CONTAINER_PACKED) {
                printf("{ listpack:\n");
                lpRepr(node->entry);
                printf("}\n");

            } else if (QL_NODE_IS_PLAIN(node)) {
                printf("{ entry : %s }\n", node->entry);
            }
            printf("}\n");
            quicklistRecompressOnly(node);
        }
        node = node->next;
    }
}

/* Create or update a bookmark in the list which will be updated to the next node
 * automatically when the one referenced gets deleted.
 * Returns 1 on success (creation of new bookmark or override of an existing one).
 * Returns 0 on failure (reached the maximum supported number of bookmarks).
 * NOTE: use short simple names, so that string compare on find is quick.
 * NOTE: bookmark creation may re-allocate the quicklist, so the input pointer
         may change and it's the caller responsibility to update the reference.
 */
//创建一个name名字的书签，如果name名字的书签已存在，则直接将书签指向的节点替换为node
int quicklistBookmarkCreate(quicklist **ql_ref, const char *name, quicklistNode *node) {
    quicklist *ql = *ql_ref;
    //判断ql是否超过最大书签个数，最大5个，超过则不能创建书签
    if (ql->bookmark_count >= QL_MAX_BM)
        return 0;
    //查名字为name的书签
    quicklistBookmark *bm = _quicklistBookmarkFindByName(ql, name);
    //如果有相同名字的书签，则直接改变书签指向的节点
    if (bm) {
        bm->node = node;
        return 1;
    }
    //如果没有同名书签，需要创建新书签，并且需要重新分配zl的大小，因为书签存储在ql的柔性数组中
    ql = zrealloc(ql, sizeof(quicklist) + (ql->bookmark_count+1) * sizeof(quicklistBookmark));
    *ql_ref = ql;
    ql->bookmarks[ql->bookmark_count].node = node;
    ql->bookmarks[ql->bookmark_count].name = zstrdup(name);
    ql->bookmark_count++;
    return 1;
}

/* Find the quicklist node referenced by a named bookmark.
 * When the bookmarked node is deleted the bookmark is updated to the next node,
 * and if that's the last node, the bookmark is deleted (so find returns NULL). */
//根据名字查找书签，如果找不到则返回NULL
quicklistNode *quicklistBookmarkFind(quicklist *ql, const char *name) {
    quicklistBookmark *bm = _quicklistBookmarkFindByName(ql, name);
    if (!bm) return NULL;
    return bm->node;
}

/* Delete a named bookmark.
 * returns 0 if bookmark was not found, and 1 if deleted.
 * Note that the bookmark memory is not freed yet, and is kept for future use. */
//根据name删除书签
int quicklistBookmarkDelete(quicklist *ql, const char *name) {
    //找到name书签
    quicklistBookmark *bm = _quicklistBookmarkFindByName(ql, name);
    if (!bm)
        return 0;
    //删除书签
    _quicklistBookmarkDelete(ql, bm);
    return 1;
}

//根据name在ql中查找书签
quicklistBookmark *_quicklistBookmarkFindByName(quicklist *ql, const char *name) {
    unsigned i;
    for (i=0; i<ql->bookmark_count; i++) {
        //如果名字相同返回书签
        if (!strcmp(ql->bookmarks[i].name, name)) {
            return &ql->bookmarks[i];
        }
    }
    return NULL;
}

//根据node节点查找书签
quicklistBookmark *_quicklistBookmarkFindByNode(quicklist *ql, quicklistNode *node) {
    unsigned i;
    for (i=0; i<ql->bookmark_count; i++) {
        //遍历指向节点相同的书签返回
        if (ql->bookmarks[i].node == node) {
            return &ql->bookmarks[i];
        }
    }
    return NULL;
}

//移除bm，原理，将bm后面的书签元素往前移动
void _quicklistBookmarkDelete(quicklist *ql, quicklistBookmark *bm) {
    int index = bm - ql->bookmarks;
    zfree(bm->name);
    ql->bookmark_count--;
    //注意：我们还没有缩小（realloc）快速列表（为了避免产生共鸣，它可能会在以后重新使用（调用realloc可能不会）。
    //将后面的元素往前移动，bm+1则是下一个元素
    memmove(bm, bm+1, (ql->bookmark_count - index)* sizeof(*bm));
    /* NOTE: We do not shrink (realloc) the quicklist yet (to avoid resonance,
     * it may be re-used later (a call to realloc may NOP). */
}
//释放quicklist中保留书签的名字指向的所占用的空间，
//但不会释放指向的quicklistBookmark数组的空间，
// 因为quicklistBookmark时结构体quicklist的空间，释放quicklist则会释放quicklistBookmark
void quicklistBookmarksClear(quicklist *ql) {
    //从尾到头迭代书签，将书签的名字所占用的空间释放
    while (ql->bookmark_count)
        zfree(ql->bookmarks[--ql->bookmark_count].name);
    /* NOTE: We do not shrink (realloc) the quick list. main use case for this
     * function is just before releasing the allocation. */
}

/* The rest of this file is test cases and test helpers. */
#ifdef REDIS_TEST
#include <stdint.h>
#include <sys/time.h>
#include "testhelp.h"
#include <stdlib.h>

#define yell(str, ...) printf("ERROR! " str "\n\n", __VA_ARGS__)

#define ERROR                                                                  \
    do {                                                                       \
        printf("\tERROR!\n");                                                  \
        err++;                                                                 \
    } while (0)

#define ERR(x, ...)                                                            \
    do {                                                                       \
        printf("%s:%s:%d:\t", __FILE__, __func__, __LINE__);                   \
        printf("ERROR! " x "\n", __VA_ARGS__);                                 \
        err++;                                                                 \
    } while (0)

#define TEST(name) printf("test — %s\n", name);
#define TEST_DESC(name, ...) printf("test — " name "\n", __VA_ARGS__);

#define QL_TEST_VERBOSE 0

#define UNUSED(x) (void)(x)
static void ql_info(quicklist *ql) {
#if QL_TEST_VERBOSE
    printf("Container length: %lu\n", ql->len);
    printf("Container size: %lu\n", ql->count);
    if (ql->head)
        printf("\t(zsize head: %lu)\n", lpLength(ql->head->entry));
    if (ql->tail)
        printf("\t(zsize tail: %lu)\n", lpLength(ql->tail->entry));
    printf("\n");
#else
    UNUSED(ql);
#endif
}

/* Return the UNIX time in microseconds */
static long long ustime(void) {
    struct timeval tv;
    long long ust;

    gettimeofday(&tv, NULL);
    ust = ((long long)tv.tv_sec) * 1000000;
    ust += tv.tv_usec;
    return ust;
}

/* Return the UNIX time in milliseconds */
static long long mstime(void) { return ustime() / 1000; }

/* Iterate over an entire quicklist.
 * Print the list if 'print' == 1.
 *
 * Returns physical count of elements found by iterating over the list. */
static int _itrprintr(quicklist *ql, int print, int forward) {
    quicklistIter *iter =
        quicklistGetIterator(ql, forward ? AL_START_HEAD : AL_START_TAIL);
    quicklistEntry entry;
    int i = 0;
    int p = 0;
    quicklistNode *prev = NULL;
    while (quicklistNext(iter, &entry)) {
        if (entry.node != prev) {
            /* Count the number of list nodes too */
            p++;
            prev = entry.node;
        }
        if (print) {
            int size = (entry.sz > (1<<20)) ? 1<<20 : entry.sz;
            printf("[%3d (%2d)]: [%.*s] (%lld)\n", i, p, size,
                   (char *)entry.value, entry.longval);
        }
        i++;
    }
    quicklistReleaseIterator(iter);
    return i;
}
static int itrprintr(quicklist *ql, int print) {
    return _itrprintr(ql, print, 1);
}

static int itrprintr_rev(quicklist *ql, int print) {
    return _itrprintr(ql, print, 0);
}

#define ql_verify(a, b, c, d, e)                                               \
    do {                                                                       \
        err += _ql_verify((a), (b), (c), (d), (e));                            \
    } while (0)

static int _ql_verify_compress(quicklist *ql) {
    int errors = 0;
    if (quicklistAllowsCompression(ql)) {
        quicklistNode *node = ql->head;
        unsigned int low_raw = ql->compress;
        unsigned int high_raw = ql->len - ql->compress;

        for (unsigned int at = 0; at < ql->len; at++, node = node->next) {
            if (node && (at < low_raw || at >= high_raw)) {
                if (node->encoding != QUICKLIST_NODE_ENCODING_RAW) {
                    yell("Incorrect compression: node %d is "
                         "compressed at depth %d ((%u, %u); total "
                         "nodes: %lu; size: %zu; recompress: %d)",
                         at, ql->compress, low_raw, high_raw, ql->len, node->sz,
                         node->recompress);
                    errors++;
                }
            } else {
                if (node->encoding != QUICKLIST_NODE_ENCODING_LZF &&
                    !node->attempted_compress) {
                    yell("Incorrect non-compression: node %d is NOT "
                         "compressed at depth %d ((%u, %u); total "
                         "nodes: %lu; size: %zu; recompress: %d; attempted: %d)",
                         at, ql->compress, low_raw, high_raw, ql->len, node->sz,
                         node->recompress, node->attempted_compress);
                    errors++;
                }
            }
        }
    }
    return errors;
}

/* Verify list metadata matches physical list contents. */
static int _ql_verify(quicklist *ql, uint32_t len, uint32_t count,
                      uint32_t head_count, uint32_t tail_count) {
    int errors = 0;

    ql_info(ql);
    if (len != ql->len) {
        yell("quicklist length wrong: expected %d, got %lu", len, ql->len);
        errors++;
    }

    if (count != ql->count) {
        yell("quicklist count wrong: expected %d, got %lu", count, ql->count);
        errors++;
    }

    int loopr = itrprintr(ql, 0);
    if (loopr != (int)ql->count) {
        yell("quicklist cached count not match actual count: expected %lu, got "
             "%d",
             ql->count, loopr);
        errors++;
    }

    int rloopr = itrprintr_rev(ql, 0);
    if (loopr != rloopr) {
        yell("quicklist has different forward count than reverse count!  "
             "Forward count is %d, reverse count is %d.",
             loopr, rloopr);
        errors++;
    }

    if (ql->len == 0 && !errors) {
        return errors;
    }

    if (ql->head && head_count != ql->head->count &&
        head_count != lpLength(ql->head->entry)) {
        yell("quicklist head count wrong: expected %d, "
             "got cached %d vs. actual %lu",
             head_count, ql->head->count, lpLength(ql->head->entry));
        errors++;
    }

    if (ql->tail && tail_count != ql->tail->count &&
        tail_count != lpLength(ql->tail->entry)) {
        yell("quicklist tail count wrong: expected %d, "
             "got cached %u vs. actual %lu",
             tail_count, ql->tail->count, lpLength(ql->tail->entry));
        errors++;
    }

    errors += _ql_verify_compress(ql);
    return errors;
}

/* Release iterator and verify compress correctly. */
static void ql_release_iterator(quicklistIter *iter) {
    quicklist *ql = NULL;
    if (iter) ql = iter->quicklist;
    quicklistReleaseIterator(iter);
    if (ql) assert(!_ql_verify_compress(ql));
}

/* Generate new string concatenating integer i against string 'prefix' */
static char *genstr(char *prefix, int i) {
    static char result[64] = {0};
    snprintf(result, sizeof(result), "%s%d", prefix, i);
    return result;
}

static void randstring(unsigned char *target, size_t sz) {
    size_t p = 0;
    int minval, maxval;
    switch(rand() % 3) {
    case 0:
        minval = 'a';
        maxval = 'z';
    break;
    case 1:
        minval = '0';
        maxval = '9';
    break;
    case 2:
        minval = 'A';
        maxval = 'Z';
    break;
    default:
        assert(NULL);
    }

    while(p < sz)
        target[p++] = minval+rand()%(maxval-minval+1);
}

/* main test, but callable from other files */
int quicklistTest(int argc, char *argv[], int flags) {
    UNUSED(argc);
    UNUSED(argv);

    int accurate = (flags & REDIS_TEST_ACCURATE);
    unsigned int err = 0;
    int optimize_start =
        -(int)(sizeof(optimization_level) / sizeof(*optimization_level));

    printf("Starting optimization offset at: %d\n", optimize_start);

    int options[] = {0, 1, 2, 3, 4, 5, 6, 10};
    int fills[] = {-5, -4, -3, -2, -1, 0,
                   1, 2, 32, 66, 128, 999};
    size_t option_count = sizeof(options) / sizeof(*options);
    int fill_count = (int)(sizeof(fills) / sizeof(*fills));
    long long runtime[option_count];

    for (int _i = 0; _i < (int)option_count; _i++) {
        printf("Testing Compression option %d\n", options[_i]);
        long long start = mstime();
        quicklistIter *iter;

        TEST("create list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("add to tail of empty list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushTail(ql, "hello", 6);
            /* 1 for head and 1 for tail because 1 node = head = tail */
            ql_verify(ql, 1, 1, 1, 1);
            quicklistRelease(ql);
        }

        TEST("add to head of empty list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, "hello", 6);
            /* 1 for head and 1 for tail because 1 node = head = tail */
            ql_verify(ql, 1, 1, 1, 1);
            quicklistRelease(ql);
        }

        TEST_DESC("add to tail 5x at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 5; i++)
                    quicklistPushTail(ql, genstr("hello", i), 32);
                if (ql->count != 5)
                    ERROR;
                if (fills[f] == 32)
                    ql_verify(ql, 1, 5, 5, 5);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("add to head 5x at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 5; i++)
                    quicklistPushHead(ql, genstr("hello", i), 32);
                if (ql->count != 5)
                    ERROR;
                if (fills[f] == 32)
                    ql_verify(ql, 1, 5, 5, 5);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("add to tail 500x at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushTail(ql, genstr("hello", i), 64);
                if (ql->count != 500)
                    ERROR;
                if (fills[f] == 32)
                    ql_verify(ql, 16, 500, 32, 20);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("add to head 500x at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushHead(ql, genstr("hello", i), 32);
                if (ql->count != 500)
                    ERROR;
                if (fills[f] == 32)
                    ql_verify(ql, 16, 500, 20, 32);
                quicklistRelease(ql);
            }
        }

        TEST("rotate empty") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistRotate(ql);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("Comprassion Plain node") {
            char buf[256];
            quicklistisSetPackedThreshold(1);
            quicklist *ql = quicklistNew(-2, 1);
            for (int i = 0; i < 500; i++) {
                /* Set to 256 to allow the node to be triggered to compress,
                 * if it is less than 48(nocompress), the test will be successful. */
                snprintf(buf, sizeof(buf), "hello%d", i);
                quicklistPushHead(ql, buf, 256);
            }

            quicklistIter *iter = quicklistGetIterator(ql, AL_START_TAIL);
            quicklistEntry entry;
            int i = 0;
            while (quicklistNext(iter, &entry)) {
                snprintf(buf, sizeof(buf), "hello%d", i);
                if (strcmp((char *)entry.value, buf))
                    ERR("value [%s] didn't match [%s] at position %d",
                        entry.value, buf, i);
                i++;
            }
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("NEXT plain node")
        {
            packed_threshold = 3;
            quicklist *ql = quicklistNew(-2, options[_i]);
            char *strings[] = {"hello1", "hello2", "h3", "h4", "hello5"};

            for (int i = 0; i < 5; ++i)
                quicklistPushHead(ql, strings[i], strlen(strings[i]));

            quicklistEntry entry;
            quicklistIter *iter = quicklistGetIterator(ql, AL_START_TAIL);
            int j = 0;

            while(quicklistNext(iter, &entry) != 0) {
                assert(strncmp(strings[j], (char *)entry.value, strlen(strings[j])) == 0);
                j++;
            }
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("rotate plain node ") {
            unsigned char *data = NULL;
            size_t sz;
            long long lv;
            int i =0;
            packed_threshold = 5;
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, "hello1", 6);
            quicklistPushHead(ql, "hello4", 6);
            quicklistPushHead(ql, "hello3", 6);
            quicklistPushHead(ql, "hello2", 6);
            quicklistRotate(ql);

            for(i = 1 ; i < 5; i++) {
                quicklistPop(ql, QUICKLIST_HEAD, &data, &sz, &lv);
                int temp_char = data[5];
                zfree(data);
                assert(temp_char == ('0' + i));
            }

            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
            packed_threshold = (1 << 30);
        }

        TEST("rotate one val once") {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                quicklistPushHead(ql, "hello", 6);
                quicklistRotate(ql);
                /* Ignore compression verify because listpack is
                 * too small to compress. */
                ql_verify(ql, 1, 1, 1, 1);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("rotate 500 val 5000 times at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                quicklistPushHead(ql, "900", 3);
                quicklistPushHead(ql, "7000", 4);
                quicklistPushHead(ql, "-1200", 5);
                quicklistPushHead(ql, "42", 2);
                for (int i = 0; i < 500; i++)
                    quicklistPushHead(ql, genstr("hello", i), 64);
                ql_info(ql);
                for (int i = 0; i < 5000; i++) {
                    ql_info(ql);
                    quicklistRotate(ql);
                }
                if (fills[f] == 1)
                    ql_verify(ql, 504, 504, 1, 1);
                else if (fills[f] == 2)
                    ql_verify(ql, 252, 504, 2, 2);
                else if (fills[f] == 32)
                    ql_verify(ql, 16, 504, 32, 24);
                quicklistRelease(ql);
            }
        }

        TEST("pop empty") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPop(ql, QUICKLIST_HEAD, NULL, NULL, NULL);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("pop 1 string from 1") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            char *populate = genstr("hello", 331);
            quicklistPushHead(ql, populate, 32);
            unsigned char *data;
            size_t sz;
            long long lv;
            ql_info(ql);
            assert(quicklistPop(ql, QUICKLIST_HEAD, &data, &sz, &lv));
            assert(data != NULL);
            assert(sz == 32);
            if (strcmp(populate, (char *)data)) {
                int size = sz;
                ERR("Pop'd value (%.*s) didn't equal original value (%s)", size,
                    data, populate);
            }
            zfree(data);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("pop head 1 number from 1") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, "55513", 5);
            unsigned char *data;
            size_t sz;
            long long lv;
            ql_info(ql);
            assert(quicklistPop(ql, QUICKLIST_HEAD, &data, &sz, &lv));
            assert(data == NULL);
            assert(lv == 55513);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("pop head 500 from 500") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            for (int i = 0; i < 500; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            ql_info(ql);
            for (int i = 0; i < 500; i++) {
                unsigned char *data;
                size_t sz;
                long long lv;
                int ret = quicklistPop(ql, QUICKLIST_HEAD, &data, &sz, &lv);
                assert(ret == 1);
                assert(data != NULL);
                assert(sz == 32);
                if (strcmp(genstr("hello", 499 - i), (char *)data)) {
                    int size = sz;
                    ERR("Pop'd value (%.*s) didn't equal original value (%s)",
                        size, data, genstr("hello", 499 - i));
                }
                zfree(data);
            }
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("pop head 5000 from 500") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            for (int i = 0; i < 500; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            for (int i = 0; i < 5000; i++) {
                unsigned char *data;
                size_t sz;
                long long lv;
                int ret = quicklistPop(ql, QUICKLIST_HEAD, &data, &sz, &lv);
                if (i < 500) {
                    assert(ret == 1);
                    assert(data != NULL);
                    assert(sz == 32);
                    if (strcmp(genstr("hello", 499 - i), (char *)data)) {
                        int size = sz;
                        ERR("Pop'd value (%.*s) didn't equal original value "
                            "(%s)",
                            size, data, genstr("hello", 499 - i));
                    }
                    zfree(data);
                } else {
                    assert(ret == 0);
                }
            }
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("iterate forward over 500 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            quicklistIter *iter = quicklistGetIterator(ql, AL_START_HEAD);
            quicklistEntry entry;
            int i = 499, count = 0;
            while (quicklistNext(iter, &entry)) {
                char *h = genstr("hello", i);
                if (strcmp((char *)entry.value, h))
                    ERR("value [%s] didn't match [%s] at position %d",
                        entry.value, h, i);
                i--;
                count++;
            }
            if (count != 500)
                ERR("Didn't iterate over exactly 500 elements (%d)", i);
            ql_verify(ql, 16, 500, 20, 32);
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("iterate reverse over 500 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            quicklistIter *iter = quicklistGetIterator(ql, AL_START_TAIL);
            quicklistEntry entry;
            int i = 0;
            while (quicklistNext(iter, &entry)) {
                char *h = genstr("hello", i);
                if (strcmp((char *)entry.value, h))
                    ERR("value [%s] didn't match [%s] at position %d",
                        entry.value, h, i);
                i++;
            }
            if (i != 500)
                ERR("Didn't iterate over exactly 500 elements (%d)", i);
            ql_verify(ql, 16, 500, 20, 32);
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("insert after 1 element") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, "hello", 6);
            quicklistEntry entry;
            iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
            quicklistInsertAfter(iter, &entry, "abc", 4);
            ql_release_iterator(iter);
            ql_verify(ql, 1, 2, 2, 2);

            /* verify results */
            iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
            int sz = entry.sz;
            if (strncmp((char *)entry.value, "hello", 5)) {
                ERR("Value 0 didn't match, instead got: %.*s", sz,
                    entry.value);
            }
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 1, &entry);
            sz = entry.sz;
            if (strncmp((char *)entry.value, "abc", 3)) {
                ERR("Value 1 didn't match, instead got: %.*s", sz,
                    entry.value);
            }
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("insert before 1 element") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, "hello", 6);
            quicklistEntry entry;
            iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
            quicklistInsertBefore(iter, &entry, "abc", 4);
            ql_release_iterator(iter);
            ql_verify(ql, 1, 2, 2, 2);

            /* verify results */
            iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
            int sz = entry.sz;
            if (strncmp((char *)entry.value, "abc", 3)) {
                ERR("Value 0 didn't match, instead got: %.*s", sz,
                    entry.value);
            }
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 1, &entry);
            sz = entry.sz;
            if (strncmp((char *)entry.value, "hello", 5)) {
                ERR("Value 1 didn't match, instead got: %.*s", sz,
                    entry.value);
            }
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("insert head while head node is full") {
            quicklist *ql = quicklistNew(4, options[_i]);
            for (int i = 0; i < 10; i++)
                quicklistPushTail(ql, genstr("hello", i), 6);
            quicklistSetFill(ql, -1);
            quicklistEntry entry;
            iter = quicklistGetIteratorEntryAtIdx(ql, -10, &entry);
            char buf[4096] = {0};
            quicklistInsertBefore(iter, &entry, buf, 4096);
            ql_release_iterator(iter);
            ql_verify(ql, 4, 11, 1, 2);
            quicklistRelease(ql);
        }

        TEST("insert tail while tail node is full") {
            quicklist *ql = quicklistNew(4, options[_i]);
            for (int i = 0; i < 10; i++)
                quicklistPushHead(ql, genstr("hello", i), 6);
            quicklistSetFill(ql, -1);
            quicklistEntry entry;
            iter = quicklistGetIteratorEntryAtIdx(ql, -1, &entry);
            char buf[4096] = {0};
            quicklistInsertAfter(iter, &entry, buf, 4096);
            ql_release_iterator(iter);
            ql_verify(ql, 4, 11, 2, 1);
            quicklistRelease(ql);
        }

        TEST_DESC("insert once in elements while iterating at compress %d",
                  options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                quicklistPushTail(ql, "abc", 3);
                quicklistSetFill(ql, 1);
                quicklistPushTail(ql, "def", 3); /* force to unique node */
                quicklistSetFill(ql, f);
                quicklistPushTail(ql, "bob", 3); /* force to reset for +3 */
                quicklistPushTail(ql, "foo", 3);
                quicklistPushTail(ql, "zoo", 3);

                itrprintr(ql, 0);
                /* insert "bar" before "bob" while iterating over list. */
                quicklistIter *iter = quicklistGetIterator(ql, AL_START_HEAD);
                quicklistEntry entry;
                while (quicklistNext(iter, &entry)) {
                    if (!strncmp((char *)entry.value, "bob", 3)) {
                        /* Insert as fill = 1 so it spills into new node. */
                        quicklistInsertBefore(iter, &entry, "bar", 3);
                        break; /* didn't we fix insert-while-iterating? */
                    }
                }
                ql_release_iterator(iter);
                itrprintr(ql, 0);

                /* verify results */
                iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
                int sz = entry.sz;

                if (strncmp((char *)entry.value, "abc", 3))
                    ERR("Value 0 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 1, &entry);
                if (strncmp((char *)entry.value, "def", 3))
                    ERR("Value 1 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 2, &entry);
                if (strncmp((char *)entry.value, "bar", 3))
                    ERR("Value 2 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 3, &entry);
                if (strncmp((char *)entry.value, "bob", 3))
                    ERR("Value 3 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 4, &entry);
                if (strncmp((char *)entry.value, "foo", 3))
                    ERR("Value 4 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 5, &entry);
                if (strncmp((char *)entry.value, "zoo", 3))
                    ERR("Value 5 didn't match, instead got: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("insert [before] 250 new in middle of 500 elements at compress %d",
                  options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushTail(ql, genstr("hello", i), 32);
                for (int i = 0; i < 250; i++) {
                    quicklistEntry entry;
                    iter = quicklistGetIteratorEntryAtIdx(ql, 250, &entry);
                    quicklistInsertBefore(iter, &entry, genstr("abc", i), 32);
                    ql_release_iterator(iter);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 25, 750, 32, 20);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("insert [after] 250 new in middle of 500 elements at compress %d",
                  options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushHead(ql, genstr("hello", i), 32);
                for (int i = 0; i < 250; i++) {
                    quicklistEntry entry;
                    iter = quicklistGetIteratorEntryAtIdx(ql, 250, &entry);
                    quicklistInsertAfter(iter, &entry, genstr("abc", i), 32);
                    ql_release_iterator(iter);
                }

                if (ql->count != 750)
                    ERR("List size not 750, but rather %ld", ql->count);

                if (fills[f] == 32)
                    ql_verify(ql, 26, 750, 20, 32);
                quicklistRelease(ql);
            }
        }

        TEST("duplicate empty list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            ql_verify(ql, 0, 0, 0, 0);
            quicklist *copy = quicklistDup(ql);
            ql_verify(copy, 0, 0, 0, 0);
            quicklistRelease(ql);
            quicklistRelease(copy);
        }

        TEST("duplicate list of 1 element") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushHead(ql, genstr("hello", 3), 32);
            ql_verify(ql, 1, 1, 1, 1);
            quicklist *copy = quicklistDup(ql);
            ql_verify(copy, 1, 1, 1, 1);
            quicklistRelease(ql);
            quicklistRelease(copy);
        }

        TEST("duplicate list of 500") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            ql_verify(ql, 16, 500, 20, 32);

            quicklist *copy = quicklistDup(ql);
            ql_verify(copy, 16, 500, 20, 32);
            quicklistRelease(ql);
            quicklistRelease(copy);
        }

        for (int f = 0; f < fill_count; f++) {
            TEST_DESC("index 1,200 from 500 list at fill %d at compress %d", f,
                      options[_i]) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushTail(ql, genstr("hello", i + 1), 32);
                quicklistEntry entry;
                iter = quicklistGetIteratorEntryAtIdx(ql, 1, &entry);
                if (strcmp((char *)entry.value, "hello2") != 0)
                    ERR("Value: %s", entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, 200, &entry);
                if (strcmp((char *)entry.value, "hello201") != 0)
                    ERR("Value: %s", entry.value);
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }

            TEST_DESC("index -1,-2 from 500 list at fill %d at compress %d",
                      fills[f], options[_i]) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushTail(ql, genstr("hello", i + 1), 32);
                quicklistEntry entry;
                iter = quicklistGetIteratorEntryAtIdx(ql, -1, &entry);
                if (strcmp((char *)entry.value, "hello500") != 0)
                    ERR("Value: %s", entry.value);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, -2, &entry);
                if (strcmp((char *)entry.value, "hello499") != 0)
                    ERR("Value: %s", entry.value);
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }

            TEST_DESC("index -100 from 500 list at fill %d at compress %d",
                      fills[f], options[_i]) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 500; i++)
                    quicklistPushTail(ql, genstr("hello", i + 1), 32);
                quicklistEntry entry;
                iter = quicklistGetIteratorEntryAtIdx(ql, -100, &entry);
                if (strcmp((char *)entry.value, "hello401") != 0)
                    ERR("Value: %s", entry.value);
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }

            TEST_DESC("index too big +1 from 50 list at fill %d at compress %d",
                      fills[f], options[_i]) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                for (int i = 0; i < 50; i++)
                    quicklistPushTail(ql, genstr("hello", i + 1), 32);
                quicklistEntry entry;
                int sz = entry.sz;
                iter = quicklistGetIteratorEntryAtIdx(ql, 50, &entry);
                if (iter)
                    ERR("Index found at 50 with 50 list: %.*s", sz,
                        entry.value);
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST("delete range empty list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistDelRange(ql, 5, 20);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("delete range of entire node in list of one node") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            for (int i = 0; i < 32; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            ql_verify(ql, 1, 32, 32, 32);
            quicklistDelRange(ql, 0, 32);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("delete range of entire node with overflow counts") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            for (int i = 0; i < 32; i++)
                quicklistPushHead(ql, genstr("hello", i), 32);
            ql_verify(ql, 1, 32, 32, 32);
            quicklistDelRange(ql, 0, 128);
            ql_verify(ql, 0, 0, 0, 0);
            quicklistRelease(ql);
        }

        TEST("delete middle 100 of 500 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            ql_verify(ql, 16, 500, 32, 20);
            quicklistDelRange(ql, 200, 100);
            ql_verify(ql, 14, 400, 32, 20);
            quicklistRelease(ql);
        }

        TEST("delete less than fill but across nodes") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            ql_verify(ql, 16, 500, 32, 20);
            quicklistDelRange(ql, 60, 10);
            ql_verify(ql, 16, 490, 32, 20);
            quicklistRelease(ql);
        }

        TEST("delete negative 1 from 500 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            ql_verify(ql, 16, 500, 32, 20);
            quicklistDelRange(ql, -1, 1);
            ql_verify(ql, 16, 499, 32, 19);
            quicklistRelease(ql);
        }

        TEST("delete negative 1 from 500 list with overflow counts") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            ql_verify(ql, 16, 500, 32, 20);
            quicklistDelRange(ql, -1, 128);
            ql_verify(ql, 16, 499, 32, 19);
            quicklistRelease(ql);
        }

        TEST("delete negative 100 from 500 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 500; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            quicklistDelRange(ql, -100, 100);
            ql_verify(ql, 13, 400, 32, 16);
            quicklistRelease(ql);
        }

        TEST("delete -10 count 5 from 50 list") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            for (int i = 0; i < 50; i++)
                quicklistPushTail(ql, genstr("hello", i + 1), 32);
            ql_verify(ql, 2, 50, 32, 18);
            quicklistDelRange(ql, -10, 5);
            ql_verify(ql, 2, 45, 32, 13);
            quicklistRelease(ql);
        }

        TEST("numbers only list read") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushTail(ql, "1111", 4);
            quicklistPushTail(ql, "2222", 4);
            quicklistPushTail(ql, "3333", 4);
            quicklistPushTail(ql, "4444", 4);
            ql_verify(ql, 1, 4, 4, 4);
            quicklistEntry entry;
            iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
            if (entry.longval != 1111)
                ERR("Not 1111, %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 1, &entry);
            if (entry.longval != 2222)
                ERR("Not 2222, %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 2, &entry);
            if (entry.longval != 3333)
                ERR("Not 3333, %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 3, &entry);
            if (entry.longval != 4444)
                ERR("Not 4444, %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, 4, &entry);
            if (iter)
                ERR("Index past elements: %lld", entry.longval);
            ql_release_iterator(iter);
            
            iter = quicklistGetIteratorEntryAtIdx(ql, -1, &entry);
            if (entry.longval != 4444)
                ERR("Not 4444 (reverse), %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, -2, &entry);
            if (entry.longval != 3333)
                ERR("Not 3333 (reverse), %lld", entry.longval);
            ql_release_iterator(iter);

            iter = quicklistGetIteratorEntryAtIdx(ql, -3, &entry);
            if (entry.longval != 2222)
                ERR("Not 2222 (reverse), %lld", entry.longval);
            ql_release_iterator(iter);
            
            iter = quicklistGetIteratorEntryAtIdx(ql, -4, &entry);
            if (entry.longval != 1111)
                ERR("Not 1111 (reverse), %lld", entry.longval);
            ql_release_iterator(iter);
            
            iter = quicklistGetIteratorEntryAtIdx(ql, -5, &entry);
            if (iter)
                ERR("Index past elements (reverse), %lld", entry.longval);
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("numbers larger list read") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistSetFill(ql, 32);
            char num[32];
            long long nums[5000];
            for (int i = 0; i < 5000; i++) {
                nums[i] = -5157318210846258176 + i;
                int sz = ll2string(num, sizeof(num), nums[i]);
                quicklistPushTail(ql, num, sz);
            }
            quicklistPushTail(ql, "xxxxxxxxxxxxxxxxxxxx", 20);
            quicklistEntry entry;
            for (int i = 0; i < 5000; i++) {
                iter = quicklistGetIteratorEntryAtIdx(ql, i, &entry);
                if (entry.longval != nums[i])
                    ERR("[%d] Not longval %lld but rather %lld", i, nums[i],
                        entry.longval);
                entry.longval = 0xdeadbeef;
                ql_release_iterator(iter);
            }
            iter = quicklistGetIteratorEntryAtIdx(ql, 5000, &entry);
            if (strncmp((char *)entry.value, "xxxxxxxxxxxxxxxxxxxx", 20))
                ERR("String val not match: %s", entry.value);
            ql_verify(ql, 157, 5001, 32, 9);
            ql_release_iterator(iter);
            quicklistRelease(ql);
        }

        TEST("numbers larger list read B") {
            quicklist *ql = quicklistNew(-2, options[_i]);
            quicklistPushTail(ql, "99", 2);
            quicklistPushTail(ql, "98", 2);
            quicklistPushTail(ql, "xxxxxxxxxxxxxxxxxxxx", 20);
            quicklistPushTail(ql, "96", 2);
            quicklistPushTail(ql, "95", 2);
            quicklistReplaceAtIndex(ql, 1, "foo", 3);
            quicklistReplaceAtIndex(ql, -1, "bar", 3);
            quicklistRelease(ql);
        }

        TEST_DESC("lrem test at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                char *words[] = {"abc", "foo", "bar",  "foobar", "foobared",
                                 "zap", "bar", "test", "foo"};
                char *result[] = {"abc", "foo",  "foobar", "foobared",
                                  "zap", "test", "foo"};
                char *resultB[] = {"abc",      "foo", "foobar",
                                   "foobared", "zap", "test"};
                for (int i = 0; i < 9; i++)
                    quicklistPushTail(ql, words[i], strlen(words[i]));

                /* lrem 0 bar */
                quicklistIter *iter = quicklistGetIterator(ql, AL_START_HEAD);
                quicklistEntry entry;
                int i = 0;
                while (quicklistNext(iter, &entry)) {
                    if (quicklistCompare(&entry, (unsigned char *)"bar", 3)) {
                        quicklistDelEntry(iter, &entry);
                    }
                    i++;
                }
                ql_release_iterator(iter);

                /* check result of lrem 0 bar */
                iter = quicklistGetIterator(ql, AL_START_HEAD);
                i = 0;
                while (quicklistNext(iter, &entry)) {
                    /* Result must be: abc, foo, foobar, foobared, zap, test,
                     * foo */
                    int sz = entry.sz;
                    if (strncmp((char *)entry.value, result[i], entry.sz)) {
                        ERR("No match at position %d, got %.*s instead of %s",
                            i, sz, entry.value, result[i]);
                    }
                    i++;
                }
                ql_release_iterator(iter);

                quicklistPushTail(ql, "foo", 3);

                /* lrem -2 foo */
                iter = quicklistGetIterator(ql, AL_START_TAIL);
                i = 0;
                int del = 2;
                while (quicklistNext(iter, &entry)) {
                    if (quicklistCompare(&entry, (unsigned char *)"foo", 3)) {
                        quicklistDelEntry(iter, &entry);
                        del--;
                    }
                    if (!del)
                        break;
                    i++;
                }
                ql_release_iterator(iter);

                /* check result of lrem -2 foo */
                /* (we're ignoring the '2' part and still deleting all foo
                 * because
                 * we only have two foo) */
                iter = quicklistGetIterator(ql, AL_START_TAIL);
                i = 0;
                size_t resB = sizeof(resultB) / sizeof(*resultB);
                while (quicklistNext(iter, &entry)) {
                    /* Result must be: abc, foo, foobar, foobared, zap, test,
                     * foo */
                    int sz = entry.sz;
                    if (strncmp((char *)entry.value, resultB[resB - 1 - i],
                                sz)) {
                        ERR("No match at position %d, got %.*s instead of %s",
                            i, sz, entry.value, resultB[resB - 1 - i]);
                    }
                    i++;
                }

                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("iterate reverse + delete at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                quicklistPushTail(ql, "abc", 3);
                quicklistPushTail(ql, "def", 3);
                quicklistPushTail(ql, "hij", 3);
                quicklistPushTail(ql, "jkl", 3);
                quicklistPushTail(ql, "oop", 3);

                quicklistEntry entry;
                quicklistIter *iter = quicklistGetIterator(ql, AL_START_TAIL);
                int i = 0;
                while (quicklistNext(iter, &entry)) {
                    if (quicklistCompare(&entry, (unsigned char *)"hij", 3)) {
                        quicklistDelEntry(iter, &entry);
                    }
                    i++;
                }
                ql_release_iterator(iter);

                if (i != 5)
                    ERR("Didn't iterate 5 times, iterated %d times.", i);

                /* Check results after deletion of "hij" */
                iter = quicklistGetIterator(ql, AL_START_HEAD);
                i = 0;
                char *vals[] = {"abc", "def", "jkl", "oop"};
                while (quicklistNext(iter, &entry)) {
                    if (!quicklistCompare(&entry, (unsigned char *)vals[i],
                                          3)) {
                        ERR("Value at %d didn't match %s\n", i, vals[i]);
                    }
                    i++;
                }
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("iterator at index test at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                char num[32];
                long long nums[5000];
                for (int i = 0; i < 760; i++) {
                    nums[i] = -5157318210846258176 + i;
                    int sz = ll2string(num, sizeof(num), nums[i]);
                    quicklistPushTail(ql, num, sz);
                }

                quicklistEntry entry;
                quicklistIter *iter =
                    quicklistGetIteratorAtIdx(ql, AL_START_HEAD, 437);
                int i = 437;
                while (quicklistNext(iter, &entry)) {
                    if (entry.longval != nums[i])
                        ERR("Expected %lld, but got %lld", entry.longval,
                            nums[i]);
                    i++;
                }
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("ltrim test A at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                char num[32];
                long long nums[5000];
                for (int i = 0; i < 32; i++) {
                    nums[i] = -5157318210846258176 + i;
                    int sz = ll2string(num, sizeof(num), nums[i]);
                    quicklistPushTail(ql, num, sz);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 1, 32, 32, 32);
                /* ltrim 25 53 (keep [25,32] inclusive = 7 remaining) */
                quicklistDelRange(ql, 0, 25);
                quicklistDelRange(ql, 0, 0);
                quicklistEntry entry;
                for (int i = 0; i < 7; i++) {
                    iter = quicklistGetIteratorEntryAtIdx(ql, i, &entry);
                    if (entry.longval != nums[25 + i])
                        ERR("Deleted invalid range!  Expected %lld but got "
                            "%lld",
                            entry.longval, nums[25 + i]);
                    ql_release_iterator(iter);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 1, 7, 7, 7);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("ltrim test B at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                /* Force-disable compression because our 33 sequential
                 * integers don't compress and the check always fails. */
                quicklist *ql = quicklistNew(fills[f], QUICKLIST_NOCOMPRESS);
                char num[32];
                long long nums[5000];
                for (int i = 0; i < 33; i++) {
                    nums[i] = i;
                    int sz = ll2string(num, sizeof(num), nums[i]);
                    quicklistPushTail(ql, num, sz);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 2, 33, 32, 1);
                /* ltrim 5 16 (keep [5,16] inclusive = 12 remaining) */
                quicklistDelRange(ql, 0, 5);
                quicklistDelRange(ql, -16, 16);
                if (fills[f] == 32)
                    ql_verify(ql, 1, 12, 12, 12);
                quicklistEntry entry;

                iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
                if (entry.longval != 5)
                    ERR("A: longval not 5, but %lld", entry.longval);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, -1, &entry);
                if (entry.longval != 16)
                    ERR("B! got instead: %lld", entry.longval);
                quicklistPushTail(ql, "bobobob", 7);
                ql_release_iterator(iter);

                iter = quicklistGetIteratorEntryAtIdx(ql, -1, &entry);
                int sz = entry.sz;
                if (strncmp((char *)entry.value, "bobobob", 7))
                    ERR("Tail doesn't match bobobob, it's %.*s instead",
                        sz, entry.value);
                ql_release_iterator(iter);

                for (int i = 0; i < 12; i++) {
                    iter = quicklistGetIteratorEntryAtIdx(ql, i, &entry);
                    if (entry.longval != nums[5 + i])
                        ERR("Deleted invalid range!  Expected %lld but got "
                            "%lld",
                            entry.longval, nums[5 + i]);
                    ql_release_iterator(iter);
                }
                quicklistRelease(ql);
            }
        }

        TEST_DESC("ltrim test C at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                char num[32];
                long long nums[5000];
                for (int i = 0; i < 33; i++) {
                    nums[i] = -5157318210846258176 + i;
                    int sz = ll2string(num, sizeof(num), nums[i]);
                    quicklistPushTail(ql, num, sz);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 2, 33, 32, 1);
                /* ltrim 3 3 (keep [3,3] inclusive = 1 remaining) */
                quicklistDelRange(ql, 0, 3);
                quicklistDelRange(ql, -29,
                                  4000); /* make sure not loop forever */
                if (fills[f] == 32)
                    ql_verify(ql, 1, 1, 1, 1);
                quicklistEntry entry;
                iter = quicklistGetIteratorEntryAtIdx(ql, 0, &entry);
                if (entry.longval != -5157318210846258173)
                    ERROR;
                ql_release_iterator(iter);
                quicklistRelease(ql);
            }
        }

        TEST_DESC("ltrim test D at compress %d", options[_i]) {
            for (int f = 0; f < fill_count; f++) {
                quicklist *ql = quicklistNew(fills[f], options[_i]);
                char num[32];
                long long nums[5000];
                for (int i = 0; i < 33; i++) {
                    nums[i] = -5157318210846258176 + i;
                    int sz = ll2string(num, sizeof(num), nums[i]);
                    quicklistPushTail(ql, num, sz);
                }
                if (fills[f] == 32)
                    ql_verify(ql, 2, 33, 32, 1);
                quicklistDelRange(ql, -12, 3);
                if (ql->count != 30)
                    ERR("Didn't delete exactly three elements!  Count is: %lu",
                        ql->count);
                quicklistRelease(ql);
            }
        }

        long long stop = mstime();
        runtime[_i] = stop - start;
    }

    /* Run a longer test of compression depth outside of primary test loop. */
    int list_sizes[] = {250, 251, 500, 999, 1000};
    long long start = mstime();
    int list_count = accurate ? (int)(sizeof(list_sizes) / sizeof(*list_sizes)) : 1;
    for (int list = 0; list < list_count; list++) {
        TEST_DESC("verify specific compression of interior nodes with %d list ",
                  list_sizes[list]) {
            for (int f = 0; f < fill_count; f++) {
                for (int depth = 1; depth < 40; depth++) {
                    /* skip over many redundant test cases */
                    quicklist *ql = quicklistNew(fills[f], depth);
                    for (int i = 0; i < list_sizes[list]; i++) {
                        quicklistPushTail(ql, genstr("hello TAIL", i + 1), 64);
                        quicklistPushHead(ql, genstr("hello HEAD", i + 1), 64);
                    }

                    for (int step = 0; step < 2; step++) {
                        /* test remove node */
                        if (step == 1) {
                            for (int i = 0; i < list_sizes[list] / 2; i++) {
                                unsigned char *data;
                                assert(quicklistPop(ql, QUICKLIST_HEAD, &data,
                                                    NULL, NULL));
                                zfree(data);
                                assert(quicklistPop(ql, QUICKLIST_TAIL, &data,
                                                    NULL, NULL));
                                zfree(data);
                            }
                        }
                        quicklistNode *node = ql->head;
                        unsigned int low_raw = ql->compress;
                        unsigned int high_raw = ql->len - ql->compress;

                        for (unsigned int at = 0; at < ql->len;
                            at++, node = node->next) {
                            if (at < low_raw || at >= high_raw) {
                                if (node->encoding != QUICKLIST_NODE_ENCODING_RAW) {
                                    ERR("Incorrect compression: node %d is "
                                        "compressed at depth %d ((%u, %u); total "
                                        "nodes: %lu; size: %zu)",
                                        at, depth, low_raw, high_raw, ql->len,
                                        node->sz);
                                }
                            } else {
                                if (node->encoding != QUICKLIST_NODE_ENCODING_LZF) {
                                    ERR("Incorrect non-compression: node %d is NOT "
                                        "compressed at depth %d ((%u, %u); total "
                                        "nodes: %lu; size: %zu; attempted: %d)",
                                        at, depth, low_raw, high_raw, ql->len,
                                        node->sz, node->attempted_compress);
                                }
                            }
                        }
                    }

                    quicklistRelease(ql);
                }
            }
        }
    }
    long long stop = mstime();

    printf("\n");
    for (size_t i = 0; i < option_count; i++)
        printf("Test Loop %02d: %0.2f seconds.\n", options[i],
               (float)runtime[i] / 1000);
    printf("Compressions: %0.2f seconds.\n", (float)(stop - start) / 1000);
    printf("\n");

    TEST("bookmark get updated to next item") {
        quicklist *ql = quicklistNew(1, 0);
        quicklistPushTail(ql, "1", 1);
        quicklistPushTail(ql, "2", 1);
        quicklistPushTail(ql, "3", 1);
        quicklistPushTail(ql, "4", 1);
        quicklistPushTail(ql, "5", 1);
        assert(ql->len==5);
        /* add two bookmarks, one pointing to the node before the last. */
        assert(quicklistBookmarkCreate(&ql, "_dummy", ql->head->next));
        assert(quicklistBookmarkCreate(&ql, "_test", ql->tail->prev));
        /* test that the bookmark returns the right node, delete it and see that the bookmark points to the last node */
        assert(quicklistBookmarkFind(ql, "_test") == ql->tail->prev);
        assert(quicklistDelRange(ql, -2, 1));
        assert(quicklistBookmarkFind(ql, "_test") == ql->tail);
        /* delete the last node, and see that the bookmark was deleted. */
        assert(quicklistDelRange(ql, -1, 1));
        assert(quicklistBookmarkFind(ql, "_test") == NULL);
        /* test that other bookmarks aren't affected */
        assert(quicklistBookmarkFind(ql, "_dummy") == ql->head->next);
        assert(quicklistBookmarkFind(ql, "_missing") == NULL);
        assert(ql->len==3);
        quicklistBookmarksClear(ql); /* for coverage */
        assert(quicklistBookmarkFind(ql, "_dummy") == NULL);
        quicklistRelease(ql);
    }

    TEST("bookmark limit") {
        int i;
        quicklist *ql = quicklistNew(1, 0);
        quicklistPushHead(ql, "1", 1);
        for (i=0; i<QL_MAX_BM; i++)
            assert(quicklistBookmarkCreate(&ql, genstr("",i), ql->head));
        /* when all bookmarks are used, creation fails */
        assert(!quicklistBookmarkCreate(&ql, "_test", ql->head));
        /* delete one and see that we can now create another */
        assert(quicklistBookmarkDelete(ql, "0"));
        assert(quicklistBookmarkCreate(&ql, "_test", ql->head));
        /* delete one and see that the rest survive */
        assert(quicklistBookmarkDelete(ql, "_test"));
        for (i=1; i<QL_MAX_BM; i++)
            assert(quicklistBookmarkFind(ql, genstr("",i)) == ql->head);
        /* make sure the deleted ones are indeed gone */
        assert(!quicklistBookmarkFind(ql, "0"));
        assert(!quicklistBookmarkFind(ql, "_test"));
        quicklistRelease(ql);
    }

    if (flags & REDIS_TEST_LARGE_MEMORY) {
        TEST("compress and decompress quicklist listpack node") {
            quicklistNode *node = quicklistCreateNode();
            node->entry = lpNew(0);

            /* Just to avoid triggering the assertion in __quicklistCompressNode(),
             * it disables the passing of quicklist head or tail node. */
            node->prev = quicklistCreateNode();
            node->next = quicklistCreateNode();
            
            /* Create a rand string */
            size_t sz = (1 << 25); /* 32MB per one entry */
            unsigned char *s = zmalloc(sz);
            randstring(s, sz);

            /* Keep filling the node, until it reaches 1GB */
            for (int i = 0; i < 32; i++) {
                node->entry = lpAppend(node->entry, s, sz);
                quicklistNodeUpdateSz(node);

                long long start = mstime();
                assert(__quicklistCompressNode(node));
                assert(__quicklistDecompressNode(node));
                printf("Compress and decompress: %zu MB in %.2f seconds.\n",
                       node->sz/1024/1024, (float)(mstime() - start) / 1000);
            }

            zfree(s);
            zfree(node->prev);
            zfree(node->next);
            zfree(node->entry);
            zfree(node);
        }

#if ULONG_MAX >= 0xffffffffffffffff
        TEST("compress and decomress quicklist plain node large than UINT32_MAX") {
            size_t sz = (1ull << 32);
            unsigned char *s = zmalloc(sz);
            randstring(s, sz);
            memcpy(s, "helloworld", 10);
            memcpy(s + sz - 10, "1234567890", 10);

            quicklistNode *node = __quicklistCreatePlainNode(s, sz);

            /* Just to avoid triggering the assertion in __quicklistCompressNode(),
             * it disables the passing of quicklist head or tail node. */
            node->prev = quicklistCreateNode();
            node->next = quicklistCreateNode();

            long long start = mstime();
            assert(__quicklistCompressNode(node));
            assert(__quicklistDecompressNode(node));
            printf("Compress and decompress: %zu MB in %.2f seconds.\n",
                   node->sz/1024/1024, (float)(mstime() - start) / 1000);

            assert(memcmp(node->entry, "helloworld", 10) == 0);
            assert(memcmp(node->entry + sz - 10, "1234567890", 10) == 0);
            zfree(node->prev);
            zfree(node->next);
            zfree(node->entry);
            zfree(node);
        }
#endif
    }

    if (!err)
        printf("ALL TESTS PASSED!\n");
    else
        ERR("Sorry, not all tests passed!  In fact, %d tests failed.", err);

    return err;
}
#endif
