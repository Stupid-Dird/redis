/* quicklist.h - A generic doubly linked quicklist implementation
 *
 * Copyright (c) 2014, Matt Stancliff <matt@genges.com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright notice,
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

#include <stdint.h> // for UINTPTR_MAX

#ifndef __QUICKLIST_H__
#define __QUICKLIST_H__

/* Node, quicklist, and Iterator are the only data structures used currently. */

/* quicklistNode is a 32 byte struct describing a listpack for a quicklist.
 * We use bit fields keep the quicklistNode at 32 bytes.
 * count: 16 bits, max 65536 (max lp bytes is 65k, so max count actually < 32k).
 * encoding: 2 bits, RAW=1, LZF=2.
 * container: 2 bits, PLAIN=1, PACKED=2.
 * recompress: 1 bit, bool, true if node is temporary decompressed for usage.
 * attempted_compress: 1 bit, boolean, used for verifying during testing.
 * extra: 10 bits, free for future use; pads out the remainder of 32 bits */
//节点、快速列表和迭代器是当前使用的唯一数据结构。quicklistNode是一个32字节的结构，
// 用于描述quicklist的列表包。我们使用位字段将quicklistNode保持在32字节。
// 计数：16位，最大65536（最大lp字节数为65k，所以最大计数实际上小于32k）。
// 编码：2位，原始=1，LZF=2。容器：2位，普通=1，打包=2。重新压缩：1位，bool，
// 如果节点临时解压缩以供使用，则为true。尝试压缩：1位，布尔值，用于测试期间的验证。
// 额外：10位，未来免费使用；将32位的剩余部分进行填充
//如果container=1，则表示是普通节点，则quicklistNode只能存储一个元素
typedef struct quicklistNode {
    //上一个节点
    struct quicklistNode *prev;
    //下一个节点
    struct quicklistNode *next;
    //指向实际节点数据，如果container=1，则entry只有一个元素
    unsigned char *entry;
    //表示未压缩的空间大小
    size_t sz;             /* entry size in bytes */
    // 节点中的元素个数
    unsigned int count : 16;     /* count of items in listpack */
    //表示是否使用LZF压缩，1表示没有，2表示压缩
    unsigned int encoding : 2;   /* RAW==1 or LZF==2 */
    //表示节点是否是ziplist，2表示ziplist保存
    unsigned int container : 2;  /* PLAIN==1 or PACKED==2 */
    //1表示等待重新压缩
    unsigned int recompress : 1; /* was this node previous compressed? */
    //测试时使用
    unsigned int attempted_compress : 1; /* node can't compress; too small */
    //未使用，留着以后扩展
    unsigned int extra : 10; /* more bits to steal for future usage */
} quicklistNode;

/* quicklistLZF is a 8+N byte struct holding 'sz' followed by 'compressed'.
 * 'sz' is byte length of 'compressed' field.
 * 'compressed' is LZF data with total (compressed) length 'sz'
 * NOTE: uncompressed length is stored in quicklistNode->sz.
 * When quicklistNode->entry is compressed, node->entry points to a quicklistLZF */
//存放节点元素列表的压缩包装体，压缩后关系为quicklist->entry->quicklistLZF
typedef struct quicklistLZF {
    //压缩后的长度，单位字节
    size_t sz; /* LZF size in bytes*/
    //压缩后的数据
    char compressed[];
} quicklistLZF;

/* Bookmarks are padded with realloc at the end of of the quicklist struct.
 * They should only be used for very big lists if thousands of nodes were the
 * excess memory usage is negligible, and there's a real need to iterate on them
 * in portions.
 * When not used, they don't add any memory overhead, but when used and then
 * deleted, some overhead remains (to avoid resonance).
 * The number of bookmarks used should be kept to minimum since it also adds
 * overhead on node deletion (searching for a bookmark to update). */
//qln的书签，方便查找节点
typedef struct quicklistBookmark {
    quicklistNode *node;
    char *name;
} quicklistBookmark;

#if UINTPTR_MAX == 0xffffffff
/* 32-bit */
#   define QL_FILL_BITS 14
#   define QL_COMP_BITS 14
#   define QL_BM_BITS 4
#elif UINTPTR_MAX == 0xffffffffffffffff
/* 64-bit */
#   define QL_FILL_BITS 16
#   define QL_COMP_BITS 16
#   define QL_BM_BITS 4 /* we can encode more, but we rather limit the user
                           since they cause performance degradation. */
#else
#   error unknown arch bits count
#endif

/* quicklist is a 40 byte struct (on 64-bit systems) describing a quicklist.
 * 'count' is the number of total entries.
 * 'len' is the number of quicklist nodes.
 * 'compress' is: 0 if compression disabled, otherwise it's the number
 *                of quicklistNodes to leave uncompressed at ends of quicklist.
 * 'fill' is the user-requested (or default) fill factor.
 * 'bookmarks are an optional feature that is used by realloc this struct,
 *      so that they don't consume memory when not used. */
//quicklist是一个40字节的结构（在64位系统上），是一个双向链表
typedef struct quicklist {
    //头节点,每个节点也是一个列表
    quicklistNode *head;
    //尾结点,每个节点也是一个列表
    quicklistNode *tail;
    //所有节点中每个元素的和=所有quliklistNode中所有元素和
    unsigned long count;        /* total count of all entries in all listpacks */
    //quicklistNodes节点数
    unsigned long len;          /* number of quicklistNodes */
    //fill成员对应的配置：list-max-ziplist-size -2
    //当数字为负数，表示以下含义：
    //-1 每个quicklistNode节点的ziplist字节大小不能超过4kb。（建议）
    //-2 每个quicklistNode节点的ziplist字节大小不能超过8kb。（默认配置）
    //-3 每个quicklistNode节点的ziplist字节大小不能超过16kb。（一般不建议）
    //-4 每个quicklistNode节点的ziplist字节大小不能超过32kb。（不建议）
    //-5 每个quicklistNode节点的ziplist字节大小不能超过64kb。（正常工作量不建议）
    signed int fill : QL_FILL_BITS;       /* fill factor for individual nodes */
    //如果已禁用压缩，则“compress”为：0，如果为1则表示首尾不压缩，如果为2则表示第一第二和倒数第一第二不压缩，以此类推
    //默认为0
    unsigned int compress : QL_COMP_BITS; /* depth of end nodes not to compress;0=off */
    //书签的最大长度，4位
    unsigned int bookmark_count: QL_BM_BITS;
    //quicklist的书签，可以引用quicklist中的quicklistNode对象，同时指定节点名，通过书签集合，可以快速的到指定名字的节点位置
    quicklistBookmark bookmarks[];
} quicklist;

//元素迭代器
typedef struct quicklistIter {
    //quicklist指向迭代的列表
    quicklist *quicklist;
    //当前的节点
    quicklistNode *current;
    //指向当前元素数据
    unsigned char *zi;
    //offset表示当前元素在节点中的偏移量
    long offset; /* offset in current listpack */
    //direction表示方向
    int direction;
} quicklistIter;

//此结构体表示一个元素并且有足够的元数据
typedef struct quicklistEntry {
    //ql
    const quicklist *quicklist;
    //qln节点
    quicklistNode *node;
    //指向的元素数据
    unsigned char *zi;
    //如果entry指向的是字符串，则value指向元素的字符串值
    unsigned char *value;
    //如果entry指向的元素为整型值，则longval存储的元素整型值
    long long longval;
    //如果entry指向的是字符串，则sz是指向字符串的长度
    size_t sz;
    //offset表示指向元素在node中的偏移量
    int offset;
} quicklistEntry;

//从ql头部弹出元素
#define QUICKLIST_HEAD 0
//从ql尾部弹出元素
#define QUICKLIST_TAIL -1

/* quicklist node encodings */
//qln的编码
#define QUICKLIST_NODE_ENCODING_RAW 1
#define QUICKLIST_NODE_ENCODING_LZF 2

/* quicklist compression disable */
#define QUICKLIST_NOCOMPRESS 0

/* quicklist container formats */
#define QUICKLIST_NODE_CONTAINER_PLAIN 1
#define QUICKLIST_NODE_CONTAINER_PACKED 2
//是普通节点，就不可能是数字了，只能是字符串
#define QL_NODE_IS_PLAIN(node) ((node)->container == QUICKLIST_NODE_CONTAINER_PLAIN)

#define quicklistNodeIsCompressed(node)                                        \
    ((node)->encoding == QUICKLIST_NODE_ENCODING_LZF)

/* Prototypes */
quicklist *quicklistCreate(void);
quicklist *quicklistNew(int fill, int compress);
void quicklistSetCompressDepth(quicklist *quicklist, int depth);
void quicklistSetFill(quicklist *quicklist, int fill);
void quicklistSetOptions(quicklist *quicklist, int fill, int depth);
void quicklistRelease(quicklist *quicklist);
int quicklistPushHead(quicklist *quicklist, void *value, const size_t sz);
int quicklistPushTail(quicklist *quicklist, void *value, const size_t sz);
void quicklistPush(quicklist *quicklist, void *value, const size_t sz,
                   int where);
void quicklistAppendListpack(quicklist *quicklist, unsigned char *zl);
void quicklistAppendPlainNode(quicklist *quicklist, unsigned char *data, size_t sz);
void quicklistInsertAfter(quicklistIter *iter, quicklistEntry *entry,
                          void *value, const size_t sz);
void quicklistInsertBefore(quicklistIter *iter, quicklistEntry *entry,
                           void *value, const size_t sz);
void quicklistDelEntry(quicklistIter *iter, quicklistEntry *entry);
void quicklistReplaceEntry(quicklistIter *iter, quicklistEntry *entry,
                           void *data, size_t sz);
int quicklistReplaceAtIndex(quicklist *quicklist, long index, void *data,
                            const size_t sz);
int quicklistDelRange(quicklist *quicklist, const long start, const long stop);
quicklistIter *quicklistGetIterator(quicklist *quicklist, int direction);
quicklistIter *quicklistGetIteratorAtIdx(quicklist *quicklist,
                                         int direction, const long long idx);
quicklistIter *quicklistGetIteratorEntryAtIdx(quicklist *quicklist, const long long index,
                                              quicklistEntry *entry);
int quicklistNext(quicklistIter *iter, quicklistEntry *entry);
void quicklistSetDirection(quicklistIter *iter, int direction);
void quicklistReleaseIterator(quicklistIter *iter);
quicklist *quicklistDup(quicklist *orig);
void quicklistRotate(quicklist *quicklist);
int quicklistPopCustom(quicklist *quicklist, int where, unsigned char **data,
                       size_t *sz, long long *sval,
                       void *(*saver)(unsigned char *data, size_t sz));
int quicklistPop(quicklist *quicklist, int where, unsigned char **data,
                 size_t *sz, long long *slong);
unsigned long quicklistCount(const quicklist *ql);
int quicklistCompare(quicklistEntry *entry, unsigned char *p2, const size_t p2_len);
size_t quicklistGetLzf(const quicklistNode *node, void **data);
void quicklistRepr(unsigned char *ql, int full);

/* bookmarks */
int quicklistBookmarkCreate(quicklist **ql_ref, const char *name, quicklistNode *node);
int quicklistBookmarkDelete(quicklist *ql, const char *name);
quicklistNode *quicklistBookmarkFind(quicklist *ql, const char *name);
void quicklistBookmarksClear(quicklist *ql);
int quicklistisSetPackedThreshold(size_t sz);

#ifdef REDIS_TEST
int quicklistTest(int argc, char *argv[], int flags);
#endif

/* Directions for iterators */
//从头开始，用于迭代器
#define AL_START_HEAD 0
//从尾开始,用于迭代器
#define AL_START_TAIL 1

#endif /* __QUICKLIST_H__ */
