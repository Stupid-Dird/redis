/* Hash Tables Implementation.
 *
 * This file implements in memory hash tables with insert/del/replace/find/
 * get-random-element operations. Hash tables will auto resize if needed
 * tables of power of two in size are used, collisions are handled by
 * chaining. See the source code for more information... :)
 *
 * Copyright (c) 2006-2012, Salvatore Sanfilippo <antirez at gmail dot com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
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

#include "fmacros.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdarg.h>
#include <limits.h>
#include <sys/time.h>

#include "dict.h"
#include "zmalloc.h"
#include "redisassert.h"

/* Using dictEnableResize() / dictDisableResize() we make possible to
 * enable/disable resizing of the hash table as needed. This is very important
 * for Redis, as we use copy-on-write and don't want to move too much memory
 * around when there is a child performing saving operations.
 *
 * Note that even when dict_can_resize is set to 0, not all resizes are
 * prevented: a hash table is still allowed to grow if the ratio between
 * the number of elements and the buckets > dict_force_resize_ratio. */
//使用dictEnableResize()和dictDisableResize()我们可以根据需要禁用哈希表的大小调整。
// 这对Redis非常重要，因为我们使用写时复制，并且不想在有孩子执行保存操作时移动太多内存。
// 请注意，即使dict_can_resize设置为0，也不是所有的大小调整都会被阻止：如果元素数和存储桶数之间的比率>dict_force_resize_比率，哈希表仍然可以增长。
static int dict_can_resize = 1;
static unsigned int dict_force_resize_ratio = 5;

/* -------------------------- private prototypes ---------------------------- */

static int _dictExpandIfNeeded(dict *d);
static signed char _dictNextExp(unsigned long size);
static long _dictKeyIndex(dict *d, const void *key, uint64_t hash, dictEntry **existing);
static int _dictInit(dict *d, dictType *type);

/* -------------------------- hash functions -------------------------------- */

//TODO dict散列函数种子
static uint8_t dict_hash_function_seed[16];

//设置dict散列函数种子
void dictSetHashFunctionSeed(uint8_t *seed) {
    memcpy(dict_hash_function_seed,seed,sizeof(dict_hash_function_seed));
}
//获取dict散列函数种子
uint8_t *dictGetHashFunctionSeed(void) {
    return dict_hash_function_seed;
}

/* The default hashing function uses SipHash implementation
 * in siphash.c. */

uint64_t siphash(const uint8_t *in, const size_t inlen, const uint8_t *k);
uint64_t siphash_nocase(const uint8_t *in, const size_t inlen, const uint8_t *k);

//TODO siphash函数，
uint64_t dictGenHashFunction(const void *key, size_t len) {
    return siphash(key,len,dict_hash_function_seed);
}
//TODO
uint64_t dictGenCaseHashFunction(const unsigned char *buf, size_t len) {
    return siphash_nocase(buf,len,dict_hash_function_seed);
}

/* ----------------------------- API implementation ------------------------- */

/* Reset hash table parameters already initialized with _dictInit()*/
//初始化ht[htidex]默认参数
static void _dictReset(dict *d, int htidx)
{
    d->ht_table[htidx] = NULL;
    d->ht_size_exp[htidx] = -1;
    d->ht_used[htidx] = 0;
}

/* Create a new hash table */
//创建ht并初始化
dict *dictCreate(dictType *type)
{
    dict *d = zmalloc(sizeof(*d));

    _dictInit(d,type);
    return d;
}

/* Initialize the hash table */
//创建2张ht并初始化
int _dictInit(dict *d, dictType *type)
{
    _dictReset(d, 0);
    _dictReset(d, 1);
    d->type = type;
    d->rehashidx = -1;
    d->pauserehash = 0;
    return DICT_OK;
}

/* Resize the table to the minimal size that contains all the elements,
 * but with the invariant of a USED/BUCKETS ratio near to <= 1 */
//将表格大小调整为包含所有元素的最小大小，
//但保持USEDBUCKETS比率接近<=1的不变量
int dictResize(dict *d)
{
    unsigned long minimal;
    //如果不能调整大小或者正在重hash，则错误返回
    if (!dict_can_resize || dictIsRehashing(d)) return DICT_ERR;
    //获取第一张ht的元素个数
    minimal = d->ht_used[0];
    //如果ht长度不能小于4，否则为4
    if (minimal < DICT_HT_INITIAL_SIZE)
        minimal = DICT_HT_INITIAL_SIZE;
    return dictExpand(d, minimal);
}

/* Expand or create the hash table,
 * when malloc_failed is non-NULL, it'll avoid panic if malloc fails (in which case it'll be set to 1).
 * Returns DICT_OK if expand was performed, and DICT_ERR if skipped. */
//ht扩容或初始化，并设置rehashidx开始位为0,size为希望扩容存储的元素个数，malloc_failed不等于NULL,则表明分配内存失败则返回错误码
//如果size小于4则初始化size为4，否则找到size的最近的2的指数作为大小
//如果ht[0]是NULL的则初始化ht[0],如果ht[0]!=NULL则初始化ht[1]
//如果malloc_failed!=NULL并且分配ht内存成功，则malloc_failed=0否则为1
//如果malloc_failed==NULL，分配内存失败，则dict初始化或者扩容的ht为NULL
int _dictExpand(dict *d, unsigned long size, int* malloc_failed)
{
    //malloc_failed如果不会NULL则置为0
    if (malloc_failed) *malloc_failed = 0;

    /* the size is invalid if it is smaller than the number of
     * elements already inside the hash table */
    //如果正常扩容，或者存储的元素大于扩容后的长度，则扩容失败
    if (dictIsRehashing(d) || d->ht_used[0] > size)
        return DICT_ERR;

    /* the new hash table */
    dictEntry **new_ht_table;
    unsigned long new_ht_used;
    //获取扩容后大小的最适合的2的次方数
    signed char new_ht_size_exp = _dictNextExp(size);

    /* Detect overflows */
    //新的长度就为刚好大于size的2的次方数
    size_t newsize = 1ul<<new_ht_size_exp;
    //如果扩容后的长度小于size，或者溢出则错误返回
    if (newsize < size || newsize * sizeof(dictEntry*) < newsize)
        return DICT_ERR;

    /* Rehashing to the same table size is not useful. */
    //扩容后的大小与原来的一致，则错误返回
    if (new_ht_size_exp == d->ht_size_exp[0]) return DICT_ERR;

    /* Allocate the new hash table and initialize all pointers to NULL */
    //如果malloc_failed!=NULL,分配新的哈希表，并将所有指针初始化为NULL
    if (malloc_failed) {
        //尝试分配ht的内存
        new_ht_table = ztrycalloc(newsize*sizeof(dictEntry*));
        //如果分配new_ht_table失败，则malloc_failed=1，则错误返回
        *malloc_failed = new_ht_table == NULL;
        //malloc_failed==1则返回错误
        if (*malloc_failed)
            return DICT_ERR;
    } else
        //分配内存
        new_ht_table = zcalloc(newsize*sizeof(dictEntry*));
    //初始化元素个数为0
    new_ht_used = 0;

    /* Is this the first initialization? If so it's not really a rehashing
     * we just set the first hash table so that it can accept keys. */
    //如果是第一次初始化，则初始化第一张ht，返回ok码
    if (d->ht_table[0] == NULL) {
        d->ht_size_exp[0] = new_ht_size_exp;
        d->ht_used[0] = new_ht_used;
        d->ht_table[0] = new_ht_table;
        return DICT_OK;
    }

    /* Prepare a second hash table for incremental rehashing */
    //如果不是第一次初始化，则初始化第二张ht，返回ok
    d->ht_size_exp[1] = new_ht_size_exp;
    d->ht_used[1] = new_ht_used;
    d->ht_table[1] = new_ht_table;
    d->rehashidx = 0;
    return DICT_OK;
}

/* return DICT_ERR if expand was not performed */
//ht扩容或初始化，size是希望的扩容后的大小
int dictExpand(dict *d, unsigned long size) {
    return _dictExpand(d, size, NULL);
}

/* return DICT_ERR if expand failed due to memory allocation failure */
//初始化或扩容ht，如果分配内存失败则返回1
int dictTryExpand(dict *d, unsigned long size) {
    int malloc_failed;
    _dictExpand(d, size, &malloc_failed);
    return malloc_failed? DICT_ERR : DICT_OK;
}

/* Performs N steps of incremental rehashing. Returns 1 if there are still
 * keys to move from the old to the new hash table, otherwise 0 is returned.
 *
 * Note that a rehashing step consists in moving a bucket (that may have more
 * than one key as we use chaining) from the old to the new hash table, however
 * since part of the hash table may be composed of empty spaces, it is not
 * guaranteed that this function will rehash even a single bucket, since it
 * will visit at max N*10 empty buckets in total, otherwise the amount of
 * work it does would be unbound and the function may block for a long time. */
//渐进式的rehahs，一次最多rehash一个桶的元素，当ht[0]的元素个数==0时，则结束rehash，并将ht[1]移动到ht[0]，ht[1]=NULL
//ht[0]的桶rehash移动到ht[1]
//n表示从dict->rehashidx经过的最多连续的NULL桶，如果经过了10*n个NULL都那么就结束此次rehash，但并非完成了rehash
//从dict->rehashidx开始遍历非NULL的桶，找到第一个非NULL桶即结束遍历，然后将ht[0][rehashidx]桶中的元素rehash到ht[1]
int dictRehash(dict *d, int n) {
    //可访问的最大空桶数,如果经过empty_visits个桶还没找到非NULL桶则结束此次rehash
    int empty_visits = n*10; /* Max number of empty buckets to visit. */
    //如果不是在重hash则返回0
    if (!dictIsRehashing(d)) return 0;
    //遍历ht[0]的桶
    while(n-- && d->ht_used[0] != 0) {
        dictEntry *de, *nextde;

        /* Note that rehashidx can't overflow as we are sure there are more
         * elements because ht[0].used != 0 */
        //ht的长度必须大于rehashidx
        assert(DICTHT_SIZE(d->ht_size_exp[0]) > (unsigned long)d->rehashidx);
        //遍历第一张ht，从rehashidx的位置开始，找到不为NULL的桶，
        // 如果超过empty_visits还找不到不为NULL则返回1
        while(d->ht_table[0][d->rehashidx] == NULL) {
            d->rehashidx++;
            if (--empty_visits == 0) return 1;
        }
        de = d->ht_table[0][d->rehashidx];
        /* Move all the keys in this bucket from the old to the new hash HT */
        //将找到的桶的所有元素移动到ht[1]中
        while(de) {
            uint64_t h;
            //获取当前桶的下一个元素，作为迭代
            nextde = de->next;
            /* Get the index in the new hash table */
            //重算hash index，将hash码与ht掩码与运算
            h = dictHashKey(d, de->key) & DICTHT_SIZE_MASK(d->ht_size_exp[1]);
            //将next指向头元素
            de->next = d->ht_table[1][h];
            //将桶的头赋值为de的地址
            d->ht_table[1][h] = de;
            //ht[0]元素-1
            d->ht_used[0]--;
            //ht[1]元素+1
            d->ht_used[1]++;
            //遍历条件
            de = nextde;
        }
        //将ht[0][d->rehashidx]=NULL，因为已经迁移到ht[1][h]中
        d->ht_table[0][d->rehashidx] = NULL;
        //重hash桶指针+!
        d->rehashidx++;
    }

    /* Check if we already rehashed the whole table... */
    //如果ht[0]已经全部重hash了，那就释放ht[0]
    if (d->ht_used[0] == 0) {
        //释放ht[0]的空间
        zfree(d->ht_table[0]);
        /* Copy the new ht onto the old one */
        //将ht[1]移动到ht[0]
        d->ht_table[0] = d->ht_table[1];
        d->ht_used[0] = d->ht_used[1];
        d->ht_size_exp[0] = d->ht_size_exp[1];
        _dictReset(d, 1);
        //重hash设为-1
        d->rehashidx = -1;
        return 0;
    }

    /* More to rehash... */
    return 1;
}
//获取当前的毫秒数
long long timeInMilliseconds(void) {
    struct timeval tv;

    gettimeofday(&tv,NULL);
    return (((long long)tv.tv_sec)*1000)+(tv.tv_usec/1000);
}

/* Rehash in ms+"delta" milliseconds. The value of "delta" is larger 
 * than 0, and is smaller than 1 in most cases. The exact upper bound 
 * depends on the running time of dictRehash(d,100).*/
//如果d->pauserehash>0则不能执行rehash
//在ms限定的毫秒数内，执行rehash，也许能在ms内完成，也许不能
int dictRehashMilliseconds(dict *d, int ms) {
    if (d->pauserehash > 0) return 0;
    //开始的毫秒数
    long long start = timeInMilliseconds();
    int rehashes = 0;

    while(dictRehash(d,100)) {
        rehashes += 100;
        //如果rehash的执行时间超过了ms则退出
        if (timeInMilliseconds()-start > ms) break;
    }
    return rehashes;
}

/* This function performs just a step of rehashing, and only if hashing has
 * not been paused for our hash table. When we have iterators in the
 * middle of a rehashing we can't mess with the two hash tables otherwise
 * some element can be missed or duplicated.
 *
 * This function is called by common lookup or update operations in the
 * dictionary so that the hash table automatically migrates from H1 to H2
 * while it is actively used. */
//d->pauserehash == 0时执行一次rehash
static void _dictRehashStep(dict *d) {
    if (d->pauserehash == 0) dictRehash(d,1);
}

/* Add an element to the target hash table */
//向目标哈希表中添加一个元素
int dictAdd(dict *d, void *key, void *val)
{
    //向ht中插入，返回插入后的entry，但entry的value为NULL
    dictEntry *entry = dictAddRaw(d,key,NULL);

    if (!entry) return DICT_ERR;
    //将value拷贝一份设置到entry中
    dictSetVal(d, entry, val);
    return DICT_OK;
}

/* Low level add or find:
 * This function adds the entry but instead of setting a value returns the
 * dictEntry structure to the user, that will make sure to fill the value
 * field as they wish.
 *
 * This function is also directly exposed to the user API to be called
 * mainly in order to store non-pointers inside the hash value, example:
 *
 * entry = dictAddRaw(dict,mykey,NULL);
 * if (entry != NULL) dictSetSignedIntegerVal(entry,1000);
 *
 * Return values:
 *
 * If key already exists NULL is returned, and "*existing" is populated
 * with the existing entry if existing is not NULL.
 *
 * If key was added, the hash entry is returned to be manipulated by the caller.
 */
//使用key创建entry插入到ht中，此时entry->value为null，并且返回entry，提供其他函数去setValue
//existing是，当插入的key存在，则将key所在的entry地址填充existing
dictEntry *dictAddRaw(dict *d, void *key, dictEntry **existing)
{
    //插入下标
    long index;
    dictEntry *entry;
    int htidx;
    //如果在正在rehash，则执行一次rehash操作
    if (dictIsRehashing(d)) _dictRehashStep(d);

    /* Get the index of the new element, or -1 if
     * the element already exists. */
    //获取key的插入桶下标，如果key已经存在，则将key所在的entry地址填充existing，并返回-1
    if ((index = _dictKeyIndex(d, key, dictHashKey(d,key), existing)) == -1)
        return NULL;

    /* Allocate the memory and store the new entry.
     * Insert the element in top, with the assumption that in a database
     * system it is more likely that recently added entries are accessed
     * more frequently. */
    //判断当前插入的dict是否在rehash，是则插入到ht[1]
    htidx = dictIsRehashing(d) ? 1 : 0;
    size_t metasize = dictMetadataSize(d);
    entry = zmalloc(sizeof(*entry) + metasize);
    if (metasize > 0) {
        //将metasize的空间置为0
        memset(dictMetadata(entry), 0, metasize);
    }
    //将新插入的指向久的头节点，然后把自己作为头
    entry->next = d->ht_table[htidx][index];
    d->ht_table[htidx][index] = entry;
    //元素+1
    d->ht_used[htidx]++;

    /* Set the hash entry fields. */
    //将key拷贝副本并设置到entry->key中
    dictSetKey(d, entry, key);
    return entry;
}

/* Add or Overwrite:
 * Add an element, discarding the old value if the key already exists.
 * Return 1 if the key was added from scratch, 0 if there was already an
 * element with such key and dictReplace() just perfor同med a value update
 * operation. */
//覆盖key相同的value，如果key不存在则插入新的key-value
int dictReplace(dict *d, void *key, void *val)
{
    dictEntry *entry, *existing, auxentry;

    /* Try to add the element. If the key
     * does not exists dictAdd will succeed. */
    //插入一个key-entry，如果key存在则existing为原来的key-value
    entry = dictAddRaw(d,key,&existing);
    //如果entry不为NULL，则说明key不存在，则是插入新的entry并返回
    if (entry) {
        //赋值value set entry->value
        dictSetVal(d, entry, val);
        return 1;
    }

    /* Set the new value and free the old one. Note that it is important
     * to do that in this order, as the value may just be exactly the same
     * as the previous one. In this context, think to reference counting,
     * you want to increment (set), and then decrement (free), and not the
     * reverse. */
    //能执行到这里表示key存在，则替换新的value值
    auxentry = *existing;
    //拷贝value的副本设置到entry->value TODO
    dictSetVal(d, existing, val);
    //销毁entry->value
    dictFreeVal(d, &auxentry);
    return 0;
}

/* Add or Find:
 * dictAddOrFind() is simply a version of dictAddRaw() that always
 * returns the hash entry of the specified key, even if the key already
 * exists and can't be added (in that case the entry of the already
 * existing key is returned.)
 *
 * See dictAddRaw() for more information. */
//使用key创建entry插入到ht中，如果key已经存在则返回key所在的entry，否则返回新的entry
dictEntry *dictAddOrFind(dict *d, void *key) {
    dictEntry *entry, *existing;
    entry = dictAddRaw(d,key,&existing);
    return entry ? entry : existing;
}

/* Search and remove an element. This is a helper function for
 * dictDelete() and dictUnlink(), please check the top comment
 * of those functions. */
//删除dict中的key所在的entry，返回entry，nofree=1表示不释放需要删除的entry空间,
static dictEntry *dictGenericDelete(dict *d, const void *key, int nofree) {
    uint64_t h, idx;
    dictEntry *he, *prevHe;
    int table;

    /* dict is empty */
    //如果ht是空的NULL返回
    if (dictSize(d) == 0) return NULL;
    //如果在rehash，则再执行一次rehash
    if (dictIsRehashing(d)) _dictRehashStep(d);
    //算出hashcode
    h = dictHashKey(d, key);
    //遍历两张ht
    for (table = 0; table <= 1; table++) {
        //获取key所在的桶位
        idx = h & DICTHT_SIZE_MASK(d->ht_size_exp[table]);
        //获取到桶的头节点
        he = d->ht_table[table][idx];
        prevHe = NULL;
        //遍历桶的所有元素
        while(he) {
            //如果key相同，则删除entry
            if (key==he->key || dictCompareKeys(d, key, he->key)) {
                /* Unlink the element from the list */
                //如果有前驱节点则需要处理前驱节点与后驱节点相连
                if (prevHe)
                    prevHe->next = he->next;
                else
                    //头节点，没前驱节点，直接将下一个节点作为头节点
                    d->ht_table[table][idx] = he->next;
                //如果nofree==0则释放entry空间
                if (!nofree) {
                    dictFreeUnlinkedEntry(d, he);
                }
                //元素个数-1
                d->ht_used[table]--;
                return he;
            }
            prevHe = he;
            he = he->next;
        }
        if (!dictIsRehashing(d)) break;
    }
    return NULL; /* not found */
}

/* Remove an element, returning DICT_OK on success or DICT_ERR if the
 * element was not found. */
//删除key所在的entry，会释放entry的空间，0表示删除ok
int dictDelete(dict *ht, const void *key) {
    return dictGenericDelete(ht,key,0) ? DICT_OK : DICT_ERR;
}

/* Remove an element from the table, but without actually releasing
 * the key, value and dictionary entry. The dictionary entry is returned
 * if the element was found (and unlinked from the table), and the user
 * should later call `dictFreeUnlinkedEntry()` with it in order to release it.
 * Otherwise if the key is not found, NULL is returned.
 *
 * This function is useful when we want to remove something from the hash
 * table but want to use its value before actually deleting the entry.
 * Without this function the pattern would require two lookups:
 *
 *  entry = dictFind(...);
 *  // Do something with entry
 *  dictDelete(dictionary,entry);
 *
 * Thanks to this function it is possible to avoid this, and use
 * instead:
 *
 * entry = dictUnlink(dictionary,entry);
 * // Do something with entry
 * dictFreeUnlinkedEntry(entry); // <- This does not need to lookup again.
 */
//将key所在的entry弹出，key所在的entry将不再ht中
dictEntry *dictUnlink(dict *d, const void *key) {
    return dictGenericDelete(d,key,1);
}

/* You need to call this function to really free the entry after a call
 * to dictUnlink(). It's safe to call this function with 'he' = NULL. */
//释放he指向的entry空间
void dictFreeUnlinkedEntry(dict *d, dictEntry *he) {
    if (he == NULL) return;
    //销毁key
    dictFreeKey(d, he);
    //销毁value
    dictFreeVal(d, he);
    //释放entry
    zfree(he);
}

/* Destroy an entire dictionary */
//毁掉ht，htidx为ht的下标，callback为销毁ht的回调函数
int _dictClear(dict *d, int htidx, void(callback)(dict*)) {
    unsigned long i;

    /* Free all the elements */
    //遍历每个桶
    for (i = 0; i < DICTHT_SIZE(d->ht_size_exp[htidx]) && d->ht_used[htidx] > 0; i++) {
        dictEntry *he, *nextHe;
        //当i=0的时候调用一次回调函数
        if (callback && (i & 65535) == 0) callback(d);
        //如果所在的桶为NULL则跳过
        if ((he = d->ht_table[htidx][i]) == NULL) continue;
        //遍历桶的所有元素
        while(he) {
            //释放每个元素
            nextHe = he->next;
            dictFreeKey(d, he);
            dictFreeVal(d, he);
            zfree(he);
            d->ht_used[htidx]--;
            he = nextHe;
        }
    }
    /* Free the table and the allocated cache structure */
    //释放ht的空间
    zfree(d->ht_table[htidx]);
    /* Re-initialize the table */
    //将dict各项设为NULL或者默认值
    _dictReset(d, htidx);
    return DICT_OK; /* never fails */
}

/* Clear & Release the hash table */
//销毁整个dict，包括ht[0]和ht[1]
void dictRelease(dict *d)
{
    //销毁ht[0]
    _dictClear(d,0,NULL);
    //销毁ht[1]
    _dictClear(d,1,NULL);
    //释放dict
    zfree(d);
}

//根据key获取entry
dictEntry *dictFind(dict *d, const void *key)
{
    dictEntry *he;
    uint64_t h, idx, table;
    //NULL停止
    if (dictSize(d) == 0) return NULL; /* dict is empty */
    //如果在rehash则执行一步rehash
    if (dictIsRehashing(d)) _dictRehashStep(d);
    //hashcode
    h = dictHashKey(d, key);
    //遍历2张ht
    for (table = 0; table <= 1; table++) {
        idx = h & DICTHT_SIZE_MASK(d->ht_size_exp[table]);
        he = d->ht_table[table][idx];
        //遍历所在桶的元素，找到元素entry并返回
        while(he) {
            if (key==he->key || dictCompareKeys(d, key, he->key))
                return he;
            he = he->next;
        }
        if (!dictIsRehashing(d)) return NULL;
    }
    return NULL;
}

//根据key获取value
void *dictFetchValue(dict *d, const void *key) {
    dictEntry *he;

    he = dictFind(d,key);
    return he ? dictGetVal(he) : NULL;
}

/* A fingerprint is a 64 bit number that represents the state of the dictionary
 * at a given time, it's just a few dict properties xored together.
 * When an unsafe iterator is initialized, we get the dict fingerprint, and check
 * the fingerprint again when the iterator is released.
 * If the two fingerprints are different it means that the user of the iterator
 * performed forbidden operations against the dictionary while iterating. */
//hash的安全校验码
unsigned long long dictFingerprint(dict *d) {
    unsigned long long integers[6], hash = 0;
    int j;

    integers[0] = (long) d->ht_table[0];
    integers[1] = d->ht_size_exp[0];
    integers[2] = d->ht_used[0];
    integers[3] = (long) d->ht_table[1];
    integers[4] = d->ht_size_exp[1];
    integers[5] = d->ht_used[1];

    /* We hash N integers by summing every successive integer with the integer
     * hashing of the previous sum. Basically:
     *
     * Result = hash(hash(hash(int1)+int2)+int3) ...
     *
     * This way the same set of integers in a different order will (likely) hash
     * to a different number. */
    for (j = 0; j < 6; j++) {
        hash += integers[j];
        /* For the hashing step we use Tomas Wang's 64 bit integer hash. */
        hash = (~hash) + (hash << 21); // hash = (hash << 21) - hash - 1;
        hash = hash ^ (hash >> 24);
        hash = (hash + (hash << 3)) + (hash << 8); // hash * 265
        hash = hash ^ (hash >> 14);
        hash = (hash + (hash << 2)) + (hash << 4); // hash * 21
        hash = hash ^ (hash >> 28);
        hash = hash + (hash << 31);
    }
    return hash;
}

//创建d的迭代器，默认执行ht[0]
dictIterator *dictGetIterator(dict *d)
{
    dictIterator *iter = zmalloc(sizeof(*iter));

    iter->d = d;
    iter->table = 0;
    iter->index = -1;
    iter->safe = 0;
    iter->entry = NULL;
    iter->nextEntry = NULL;
    return iter;
}

//获取安全的迭代器
dictIterator *dictGetSafeIterator(dict *d) {
    dictIterator *i = dictGetIterator(d);

    i->safe = 1;
    return i;
}

//获取迭代器的下一个指向的entry并返回
dictEntry *dictNext(dictIterator *iter)
{
    //死循环
    while (1) {
        //如果当前指向的entry为NULL
        if (iter->entry == NULL) {
            //安全的迭代器实现，如果safe>0则暂停rehash
            if (iter->index == -1 && iter->table == 0) {
                if (iter->safe)
                    dictPauseRehashing(iter->d);
                else
                    iter->fingerprint = dictFingerprint(iter->d);
            }
            iter->index++;
            //如果iter指向的元素超出ht的范围，则将table++，index=0，从ht[1]中获取元素，前提是dict必须在rehash
            if (iter->index >= (long) DICTHT_SIZE(iter->d->ht_size_exp[iter->table])) {
                if (dictIsRehashing(iter->d) && iter->table == 0) {
                    iter->table++;
                    iter->index = 0;
                } else {
                    break;
                }
            }
            //获取iter指向的entry
            iter->entry = iter->d->ht_table[iter->table][iter->index];
        } else {
            //如果当前指向entry不为NULL，则直接获取下一个entry
            iter->entry = iter->nextEntry;
        }
        //设置迭代器的下一个元素entry
        if (iter->entry) {
            /* We need to save the 'next' here, the iterator user
             * may delete the entry we are returning. */
            iter->nextEntry = iter->entry->next;
            return iter->entry;
        }
    }
    return NULL;
}
//释放iter
void dictReleaseIterator(dictIterator *iter)
{
    if (!(iter->index == -1 && iter->table == 0)) {
        if (iter->safe)
            //恢复rehash标志位
            dictResumeRehashing(iter->d);
        else
            assert(iter->fingerprint == dictFingerprint(iter->d));
    }
    //释放iter
    zfree(iter);
}

/* Return a random entry from the hash table. Useful to
 * implement randomized algorithms */
//从哈希表中返回一个随机项。
//先随机桶，后随机桶的链表，如果在rehash则从2张表中随机桶
dictEntry *dictGetRandomKey(dict *d)
{
    dictEntry *he, *orighe;
    unsigned long h;
    int listlen, listele;
    //如果dict中为NULL，则返回
    if (dictSize(d) == 0) return NULL;
    //如果在rehash，则执行一步rehash
    if (dictIsRehashing(d)) _dictRehashStep(d);
    //获取到一个随机的桶，可能在ht[0]也可能在ht[1]
    //如果在rehash
    if (dictIsRehashing(d)) {
        //ht[0]的数组长度
        unsigned long s0 = DICTHT_SIZE(d->ht_size_exp[0]);
        do {
            /* We are sure there are no elements in indexes from 0
             * to rehashidx-1 */
            //如果在rehash，那么0-rehashidx的桶均没元素
            //所以我们使用随机数和剩余桶做hash
            h = d->rehashidx + (randomULong() % (dictSlots(d) - d->rehashidx));
            //如果h大于ht[0]的长度，则在ht[1]中获取元素
            he = (h >= s0) ? d->ht_table[1][h - s0] : d->ht_table[0][h];
        } while(he == NULL);
    } else {
        //没在rehash则直接随机数掩码运算获取桶
        unsigned long m = DICTHT_SIZE_MASK(d->ht_size_exp[0]);
        do {
            h = randomULong() & m;
            he = d->ht_table[0][h];
        } while(he == NULL);
    }

    /* Now we found a non empty bucket, but it is a linked
     * list and we need to get a random element from the list.
     * The only sane way to do so is counting the elements and
     * select a random index. */
    listlen = 0;
    orighe = he;
    //计算桶里的元素个数，listlen为元素个数
    while(he) {
        he = he->next;
        listlen++;
    }
    //随机获取链表中的一个元素下标
    listele = random() % listlen;
    he = orighe;
    //找到指向下标的元素，返回
    while(listele--) he = he->next;
    return he;
}

/* This function samples the dictionary to return a few keys from random
 * locations.
 *
 * It does not guarantee to return all the keys specified in 'count', nor
 * it does guarantee to return non-duplicated elements, however it will make
 * some effort to do both things.
 *
 * Returned pointers to hash table entries are stored into 'des' that
 * points to an array of dictEntry pointers. The array must have room for
 * at least 'count' elements, that is the argument we pass to the function
 * to tell how many random elements we need.
 *
 * The function returns the number of items stored into 'des', that may
 * be less than 'count' if the hash table has less than 'count' elements
 * inside, or if not enough elements were found in a reasonable amount of
 * steps.
 *
 * Note that this function is not suitable when you need a good distribution
 * of the returned items, but only when you need to "sample" a given number
 * of continuous elements to run some kind of algorithm or to produce
 * statistics. However the function is much faster than dictGetRandomKey()
 * at producing N elements. */
//从随机的桶中返回count个元素，但不保证能返回count个元素，也不能保证返回的元素不重复，返回的元素存储到des中，des至少有count个长度
//工作原理
//循环从随机桶开始搜集元素，例如随机点是1，则从1这个桶搜集，一直搜集到满足count个元素
//但如果循环了10count次都没有搜集到cunt个元素，则停止循环，并返回
//如果在搜集过程中，存在连续的空桶并超过5同时又超过count，那么重新生成随机桶，继续重复上面的步骤
//注意，随机桶的生成，在rehash的dict中,如果随机点小于rehashidx，则会去第二张表获取桶
unsigned int dictGetSomeKeys(dict *d, dictEntry **des, unsigned int count) {
    unsigned long j; /* internal hash table id, 0 or 1. */
    unsigned long tables; /* 1 or 2 tables? */
    unsigned long stored = 0, maxsizemask;
    unsigned long maxsteps;
    //如果取元素的个数超过整个字段元素，则取整个字典元素
    if (dictSize(d) < count) count = dictSize(d);
    //最大步骤为count的10倍
    maxsteps = count*10;

    /* Try to do a rehashing work proportional to 'count'. */
    //试着做一个与“计数”成比例的再灰化工作。
    for (j = 0; j < count; j++) {
        if (dictIsRehashing(d))
            _dictRehashStep(d);
        else
            break;
    }

    //如果在rehash，则判断ht[1]是不是大于ht[0],如果大于，则maxsizemask为ht[1]的掩码
    tables = dictIsRehashing(d) ? 2 : 1;
    maxsizemask = DICTHT_SIZE_MASK(d->ht_size_exp[0]);
    if (tables > 1 && maxsizemask < DICTHT_SIZE_MASK(d->ht_size_exp[1]))
        maxsizemask = DICTHT_SIZE_MASK(d->ht_size_exp[1]);

    /* Pick a random point inside the larger table. */
    //在较大的表格中选择一个随机点
    unsigned long i = randomULong() & maxsizemask;
    //连续空桶的个数
    unsigned long emptylen = 0; /* Continuous empty entries so far. */
    //循环收集从随机点开始的元素，当收集到count个，或者超过maxsteps次步骤循环后结束函数
    while(stored < count && maxsteps--) {
        //遍历ht[0]和ht[1]，
        for (j = 0; j < tables; j++) {
            /* Invariant of the dict.c rehashing: up to the indexes already
             * visited in ht[0] during the rehashing, there are no populated
             * buckets, so we can skip ht[0] for indexes between 0 and idx-1. */
            //0到rehashidx间没有桶，i如果小于rehashidx则跳过这个区间
            if (tables == 2 && j == 0 && i < (unsigned long) d->rehashidx) {
                /* Moreover, if we are currently out of range in the second
                 * table, there will be no elements in both tables up to
                 * the current rehashing index, so we jump if possible.
                 * (this happens when going from big to small table). */
                if (i >= DICTHT_SIZE(d->ht_size_exp[1]))
                    i = d->rehashidx;
                else
                    continue;
            }
            //如果随机点超过ht[j]则继续下一轮循环，则是判断ht[j+1]
            if (i >= DICTHT_SIZE(d->ht_size_exp[j])) continue; /* Out of range for this table. */
            //获取随机点所在的桶
            dictEntry *he = d->ht_table[j][i];

            /* Count contiguous empty buckets, and jump to other
             * locations if they reach 'count' (with a minimum of 5). */
            //判断随机桶是否为NULL，如果为NULL，则emptylen++，当emptylen >= 5 && emptylen > count则重新随机点
            if (he == NULL) {
                emptylen++;
                if (emptylen >= 5 && emptylen > count) {
                    i = randomULong() & maxsizemask;
                    emptylen = 0;
                }
            } else {
                emptylen = 0;
                //将随机桶的元素都收集到des中，当stored等于count时结束函数
                while (he) {
                    /* Collect all the elements of the buckets found non
                     * empty while iterating. */
                    *des = he;
                    des++;
                    he = he->next;
                    stored++;
                    if (stored == count) return stored;
                }
            }
        }
        //获取随机桶+1位旁边的桶，作为下一个搜集的桶
        i = (i+1) & maxsizemask;
    }
    return stored;
}

/* This is like dictGetRandomKey() from the POV of the API, but will do more
 * work to ensure a better distribution of the returned element.
 *
 * This function improves the distribution because the dictGetRandomKey()
 * problem is that it selects a random bucket, then it selects a random
 * element from the chain in the bucket. However elements being in different
 * chain lengths will have different probabilities of being reported. With
 * this function instead what we do is to consider a "linear" range of the table
 * that may be constituted of N buckets with chains of different lengths
 * appearing one after the other. Then we report a random element in the range.
 * In this way we smooth away the problem of different chain lengths. */
#define GETFAIR_NUM_ENTRIES 15
//dictGetRandomKey的改进版，不同之处，在于它随机一个范围，是跨多个桶，然后在这个新的范围集合中返回随机的元素
dictEntry *dictGetFairRandomKey(dict *d) {
    dictEntry *entries[GETFAIR_NUM_ENTRIES];
    unsigned int count = dictGetSomeKeys(d,entries,GETFAIR_NUM_ENTRIES);
    /* Note that dictGetSomeKeys() may return zero elements in an unlucky
     * run() even if there are actually elements inside the hash table. So
     * when we get zero, we call the true dictGetRandomKey() that will always
     * yield the element if the hash table has at least one. */
    if (count == 0) return dictGetRandomKey(d);
    unsigned int idx = rand() % count;
    return entries[idx];
}

/* Function to reverse bits. Algorithm from:
 * http://graphics.stanford.edu/~seander/bithacks.html#ReverseParallel */
//将v反转
static unsigned long rev(unsigned long v) {
    //获取比特位长度
    unsigned long s = CHAR_BIT * sizeof(v); // bit size; must be power of 2
    unsigned long mask = ~0UL;
    while ((s >>= 1) > 0) {
        mask ^= (mask << s);
        v = ((v >> s) & mask) | ((v << s) & ~mask);
    }
    return v;
}

/* dictScan() is used to iterate over the elements of a dictionary.
 *
 * Iterating works the following way:
 *
 * 1) Initially you call the function using a cursor (v) value of 0.
 * 2) The function performs one step of the iteration, and returns the
 *    new cursor value you must use in the next call.
 * 3) When the returned cursor is 0, the iteration is complete.
 *
 * The function guarantees all elements present in the
 * dictionary get returned between the start and end of the iteration.
 * However it is possible some elements get returned multiple times.
 *
 * For every element returned, the callback argument 'fn' is
 * called with 'privdata' as first argument and the dictionary entry
 * 'de' as second argument.
 *
 * HOW IT WORKS.
 *
 * The iteration algorithm was designed by Pieter Noordhuis.
 * The main idea is to increment a cursor starting from the higher order
 * bits. That is, instead of incrementing the cursor normally, the bits
 * of the cursor are reversed, then the cursor is incremented, and finally
 * the bits are reversed again.
 *
 * This strategy is needed because the hash table may be resized between
 * iteration calls.
 *
 * dict.c hash tables are always power of two in size, and they
 * use chaining, so the position of an element in a given table is given
 * by computing the bitwise AND between Hash(key) and SIZE-1
 * (where SIZE-1 is always the mask that is equivalent to taking the rest
 *  of the division between the Hash of the key and SIZE).
 *
 * For example if the current hash table size is 16, the mask is
 * (in binary) 1111. The position of a key in the hash table will always be
 * the last four bits of the hash output, and so forth.
 *
 * WHAT HAPPENS IF THE TABLE CHANGES IN SIZE?
 *
 * If the hash table grows, elements can go anywhere in one multiple of
 * the old bucket: for example let's say we already iterated with
 * a 4 bit cursor 1100 (the mask is 1111 because hash table size = 16).
 *
 * If the hash table will be resized to 64 elements, then the new mask will
 * be 111111. The new buckets you obtain by substituting in ??1100
 * with either 0 or 1 can be targeted only by keys we already visited
 * when scanning the bucket 1100 in the smaller hash table.
 *
 * By iterating the higher bits first, because of the inverted counter, the
 * cursor does not need to restart if the table size gets bigger. It will
 * continue iterating using cursors without '1100' at the end, and also
 * without any other combination of the final 4 bits already explored.
 *
 * Similarly when the table size shrinks over time, for example going from
 * 16 to 8, if a combination of the lower three bits (the mask for size 8
 * is 111) were already completely explored, it would not be visited again
 * because we are sure we tried, for example, both 0111 and 1111 (all the
 * variations of the higher bit) so we don't need to test it again.
 *
 * WAIT... YOU HAVE *TWO* TABLES DURING REHASHING!
 *
 * Yes, this is true, but we always iterate the smaller table first, then
 * we test all the expansions of the current cursor into the larger
 * table. For example if the current cursor is 101 and we also have a
 * larger table of size 16, we also test (0)101 and (1)101 inside the larger
 * table. This reduces the problem back to having only one table, where
 * the larger one, if it exists, is just an expansion of the smaller one.
 *
 * LIMITATIONS
 *
 * This iterator is completely stateless, and this is a huge advantage,
 * including no additional memory used.
 *
 * The disadvantages resulting from this design are:
 *
 * 1) It is possible we return elements more than once. However this is usually
 *    easy to deal with in the application level.
 * 2) The iterator must return multiple elements per call, as it needs to always
 *    return all the keys chained in a given bucket, and all the expansions, so
 *    we are sure we don't miss keys moving during rehashing.
 * 3) The reverse cursor is somewhat hard to understand at first, but this
 *    comment is supposed to help.
 */
//扫码v指向的桶
//bucketfn为桶扫码函数
//fn为元素扫码函数
unsigned long dictScan(dict *d,
                       unsigned long v,
                       dictScanFunction *fn,
                       dictScanBucketFunction* bucketfn,
                       void *privdata)
{
    int htidx0, htidx1;
    const dictEntry *de, *next;
    unsigned long m0, m1;
    //如果dict没有元素，结束返回0
    if (dictSize(d) == 0) return 0;

    /* This is needed in case the scan callback tries to do dictFind or alike. */
    //暂停rehash
    dictPauseRehashing(d);
    //如果没有在rehash，则
    if (!dictIsRehashing(d)) {
        htidx0 = 0;
        m0 = DICTHT_SIZE_MASK(d->ht_size_exp[htidx0]);

        /* Emit entries at cursor */
        //桶扫码
        if (bucketfn) bucketfn(d, &d->ht_table[htidx0][v & m0]);
        //获取桶的首元素
        de = d->ht_table[htidx0][v & m0];
        //遍历桶元素
        while (de) {
            next = de->next;
            //元素扫码函数！
            fn(privdata, de);
            de = next;
        }

        /* Set unmasked bits so incrementing the reversed cursor
         * operates on the masked bits */
        v |= ~m0;

        /* Increment the reverse cursor */
        v = rev(v);
        v++;
        v = rev(v);

    } else {
        htidx0 = 0;
        htidx1 = 1;

        /* Make sure t0 is the smaller and t1 is the bigger table */
        if (DICTHT_SIZE(d->ht_size_exp[htidx0]) > DICTHT_SIZE(d->ht_size_exp[htidx1])) {
            htidx0 = 1;
            htidx1 = 0;
        }

        m0 = DICTHT_SIZE_MASK(d->ht_size_exp[htidx0]);
        m1 = DICTHT_SIZE_MASK(d->ht_size_exp[htidx1]);

        /* Emit entries at cursor */
        if (bucketfn) bucketfn(d, &d->ht_table[htidx0][v & m0]);
        de = d->ht_table[htidx0][v & m0];
        while (de) {
            next = de->next;
            fn(privdata, de);
            de = next;
        }

        /* Iterate over indices in larger table that are the expansion
         * of the index pointed to by the cursor in the smaller table */
        do {
            /* Emit entries at cursor */
            if (bucketfn) bucketfn(d, &d->ht_table[htidx1][v & m1]);
            de = d->ht_table[htidx1][v & m1];
            while (de) {
                next = de->next;
                fn(privdata, de);
                de = next;
            }

            /* Increment the reverse cursor not covered by the smaller mask.*/
            v |= ~m1;
            v = rev(v);
            v++;
            v = rev(v);

            /* Continue while bits covered by mask difference is non-zero */
        } while (v & (m0 ^ m1));
    }
    //恢复rehash
    dictResumeRehashing(d);

    return v;
}

/* ------------------------- private functions ------------------------------ */

/* Because we may need to allocate huge memory chunk at once when dict
 * expands, we will check this allocation is allowed or not if the dict
 * type has expandAllowed member function. */
//因为当dict扩展时，我们可能需要一次分配巨大的内存块，所以要检查是否允许扩展
//如果d->type->expandAllowed == NULL则始终允许扩展
//否则，则调用expandAllowed函数，判断是否允许扩展
static int dictTypeExpandAllowed(dict *d) {
    //如果为NULL始终允许扩展
    if (d->type->expandAllowed == NULL) return 1;
    //传入元素+1算出最合适的指数,再用指数算出新的ht长度，作为新的空间，第二个参数则为元素与现有桶的比率
    return d->type->expandAllowed(
                    DICTHT_SIZE(_dictNextExp(d->ht_used[0] + 1)) * sizeof(dictEntry*),
                    (double)d->ht_used[0] / DICTHT_SIZE(d->ht_size_exp[0]));
}

/* Expand the hash table if needed */
//判断ht是否需要扩容，如果需要则扩容，如果ht为空，则初试化，需要满足以下扩容条件
//1.元素与桶的比例大于1(必选条件)
//2.dict_can_resize=1 ，并且dict的判断是否能扩展函数expandAllowed为NULL或者判断扩展函数expandAllowed返回1(2，3任满足其一)
//3.元素与ht长度比大于5:1,并且dict的判断是否能扩展函数expandAllowed为NULL或者判断扩展函数expandAllowed返回1(2，3任满足其一)
static int _dictExpandIfNeeded(dict *d)
{
    /* Incremental rehashing already in progress. Return. */
    if (dictIsRehashing(d)) return DICT_OK;

    /* If the hash table is empty expand it to the initial size. */
    //如果ht[0]为空，则初始化ht[0]
    if (DICTHT_SIZE(d->ht_size_exp[0]) == 0) return dictExpand(d, DICT_HT_INITIAL_SIZE);

    /* If we reached the 1:1 ratio, and we are allowed to resize the hash
     * table (global setting) or we should avoid it but the ratio between
     * elements/buckets is over the "safe" threshold, we resize doubling
     * the number of buckets. */
    //如果元素个数大于等于ht[0]的长度并且达到以下条件之一，则可以扩容
    //1.dict_can_resize=1 ，并且dict的判断是否能扩展函数expandAllowed为NULL或者判断扩展函数expandAllowed返回1
    //2.元素与ht长度比大于5:1,并且dict的判断是否能扩展函数expandAllowed为NULL或者判断扩展函数expandAllowed返回1
    if (d->ht_used[0] >= DICTHT_SIZE(d->ht_size_exp[0]) &&
        (dict_can_resize ||
         d->ht_used[0]/ DICTHT_SIZE(d->ht_size_exp[0]) > dict_force_resize_ratio) &&
        dictTypeExpandAllowed(d))
    {
        //ht扩展,希望扩展为元素+1
        return dictExpand(d, d->ht_used[0] + 1);
    }
    return DICT_OK;
}

/* TODO: clz optimization */
/* Our hash table capability is a power of two */
//ht的长度必须是2的次方，所以，需要将扩容大小size进行处理，返回他是2的几次方
//1.当size大于long的最大值则返回8个long大小-1(64位电脑上为64-1)次方
//2.如果size小于4等于4，则返回2次方
//3.循环找到刚好大于size的2的次方，例如100,则返回7，2的7次方为128
static signed char _dictNextExp(unsigned long size)
{
    unsigned char e = DICT_HT_INITIAL_EXP;

    if (size >= LONG_MAX) return (8*sizeof(long)-1);
    while(1) {
        if (((unsigned long)1<<e) >= size)
            return e;
        e++;
    }
}

/* Returns the index of a free slot that can be populated with
 * a hash entry for the given 'key'.
 * If the key already exists, -1 is returned
 * and the optional output parameter may be filled.
 *
 * Note that if we are in the process of rehashing the hash table, the
 * index is always returned in the context of the second (new) hash table. */
//返回可用插槽的索引，可用给定“key”的哈希项填充该插槽。
//如果ht达到扩展条件则会扩展ht，变成正在rehash
//如果key已经存在，则返回-1，并且将key所在的entry填充到existing
//请注意，如果我们正在对哈希表进行重新灰化，那么索引总是在第二个（新）哈希表的上下文中返回。
static long _dictKeyIndex(dict *d, const void *key, uint64_t hash, dictEntry **existing)
{
    unsigned long idx, table;
    dictEntry *he;
    //existing!=NULL则置为NULL
    if (existing) *existing = NULL;

    /* Expand the hash table if needed */
    //判断ht是否需要扩展，如果满足扩展条件，则扩展，重hash
    if (_dictExpandIfNeeded(d) == DICT_ERR)
        return -1;
    //遍历2张ht，ht[0]和ht[1]
    for (table = 0; table <= 1; table++) {
        //计算hash index=hash&ht.size
        idx = hash & DICTHT_SIZE_MASK(d->ht_size_exp[table]);
        /* Search if this slot does not already contain the given key */
        //获取到hash桶
        he = d->ht_table[table][idx];
        //遍历桶元素,
        while(he) {
            //判断key是否相同
            if (key==he->key || dictCompareKeys(d, key, he->key)) {
                if (existing) *existing = he;
                return -1;
            }
            //链条遍历条件
            he = he->next;
        }
        //如果不是在rehash则，从第一张ht找到插入的位置后返回，如果在rehash则总是返回第二张ht的插入位置
        if (!dictIsRehashing(d)) break;
    }
    return idx;
}

//清空dict的属性
//callback为清空ht时的回调
void dictEmpty(dict *d, void(callback)(dict*)) {
    _dictClear(d,0,callback);
    _dictClear(d,1,callback);
    d->rehashidx = -1;
    d->pauserehash = 0;
}

//启用ht的大小调整
void dictEnableResize(void) {
    dict_can_resize = 1;
}

//禁用ht的大小调整,如果元素数和存储桶数之间的比率>dict_force_resize_比率，哈希表仍然可以增长
void dictDisableResize(void) {
    dict_can_resize = 0;
}

//获取key的hash
uint64_t dictGetHash(dict *d, const void *key) {
    return dictHashKey(d, key);
}

/* Finds the dictEntry reference by using pointer and pre-calculated hash.
 * oldkey is a dead pointer and should not be accessed.
 * the hash value should be provided using dictGetHash.
 * no string / key comparison is performed.
 * return value is the reference to the dictEntry if found, or NULL if not found. */
//通过提前计算好的hash和lodptr指向的key来查找元素
dictEntry **dictFindEntryRefByPtrAndHash(dict *d, const void *oldptr, uint64_t hash) {
    dictEntry *he, **heref;
    unsigned long idx, table;
    //空返回
    if (dictSize(d) == 0) return NULL; /* dict is empty */
    //遍历2张ht
    for (table = 0; table <= 1; table++) {
        idx = hash & DICTHT_SIZE_MASK(d->ht_size_exp[table]);
        heref = &d->ht_table[table][idx];
        he = *heref;
        //迭代桶里元素
        while(he) {
            //相等返回
            if (oldptr==he->key)
                return heref;
            heref = &he->next;
            he = *heref;
        }
        if (!dictIsRehashing(d)) return NULL;
    }
    return NULL;
}

/* ------------------------------- Debugging ---------------------------------*/

#define DICT_STATS_VECTLEN 50
//输出dict的相关信息到buf中
size_t _dictGetStatsHt(char *buf, size_t bufsize, dict *d, int htidx) {
    unsigned long i, slots = 0, chainlen, maxchainlen = 0;
    unsigned long totchainlen = 0;
    unsigned long clvector[DICT_STATS_VECTLEN];
    size_t l = 0;

    if (d->ht_used[htidx] == 0) {
        return snprintf(buf,bufsize,
            "No stats available for empty dictionaries\n");
    }

    /* Compute stats. */
    for (i = 0; i < DICT_STATS_VECTLEN; i++) clvector[i] = 0;
    for (i = 0; i < DICTHT_SIZE(d->ht_size_exp[htidx]); i++) {
        dictEntry *he;

        if (d->ht_table[htidx][i] == NULL) {
            clvector[0]++;
            continue;
        }
        slots++;
        /* For each hash entry on this slot... */
        chainlen = 0;
        he = d->ht_table[htidx][i];
        while(he) {
            chainlen++;
            he = he->next;
        }
        clvector[(chainlen < DICT_STATS_VECTLEN) ? chainlen : (DICT_STATS_VECTLEN-1)]++;
        if (chainlen > maxchainlen) maxchainlen = chainlen;
        totchainlen += chainlen;
    }

    /* Generate human readable stats. */
    l += snprintf(buf+l,bufsize-l,
        "Hash table %d stats (%s):\n"
        " table size: %lu\n"
        " number of elements: %lu\n"
        " different slots: %lu\n"
        " max chain length: %lu\n"
        " avg chain length (counted): %.02f\n"
        " avg chain length (computed): %.02f\n"
        " Chain length distribution:\n",
        htidx, (htidx == 0) ? "main hash table" : "rehashing target",
        DICTHT_SIZE(d->ht_size_exp[htidx]), d->ht_used[htidx], slots, maxchainlen,
        (float)totchainlen/slots, (float)d->ht_used[htidx]/slots);

    for (i = 0; i < DICT_STATS_VECTLEN-1; i++) {
        if (clvector[i] == 0) continue;
        if (l >= bufsize) break;
        l += snprintf(buf+l,bufsize-l,
            "   %ld: %ld (%.02f%%)\n",
            i, clvector[i], ((float)clvector[i]/DICTHT_SIZE(d->ht_size_exp[htidx]))*100);
    }

    /* Unlike snprintf(), return the number of characters actually written. */
    if (bufsize) buf[bufsize-1] = '\0';
    return strlen(buf);
}

//输出dict相关信息到buf中
void dictGetStats(char *buf, size_t bufsize, dict *d) {
    size_t l;
    char *orig_buf = buf;
    size_t orig_bufsize = bufsize;

    l = _dictGetStatsHt(buf,bufsize,d,0);
    buf += l;
    bufsize -= l;
    if (dictIsRehashing(d) && bufsize > 0) {
        _dictGetStatsHt(buf,bufsize,d,1);
    }
    /* Make sure there is a NULL term at the end. */
    if (orig_bufsize) orig_buf[orig_bufsize-1] = '\0';
}

/* ------------------------------- Benchmark ---------------------------------*/

#ifdef REDIS_TEST
#include "testhelp.h"

#define UNUSED(V) ((void) V)

uint64_t hashCallback(const void *key) {
    return dictGenHashFunction((unsigned char*)key, strlen((char*)key));
}

int compareCallback(dict *d, const void *key1, const void *key2) {
    int l1,l2;
    UNUSED(d);

    l1 = strlen((char*)key1);
    l2 = strlen((char*)key2);
    if (l1 != l2) return 0;
    return memcmp(key1, key2, l1) == 0;
}

void freeCallback(dict *d, void *val) {
    UNUSED(d);

    zfree(val);
}

char *stringFromLongLong(long long value) {
    char buf[32];
    int len;
    char *s;

    len = sprintf(buf,"%lld",value);
    s = zmalloc(len+1);
    memcpy(s, buf, len);
    s[len] = '\0';
    return s;
}

dictType BenchmarkDictType = {
    hashCallback,
    NULL,
    NULL,
    compareCallback,
    freeCallback,
    NULL,
    NULL
};

#define start_benchmark() start = timeInMilliseconds()
#define end_benchmark(msg) do { \
    elapsed = timeInMilliseconds()-start; \
    printf(msg ": %ld items in %lld ms\n", count, elapsed); \
} while(0)

/* ./redis-server test dict [<count> | --accurate] */
int dictTest(int argc, char **argv, int flags) {
    long j;
    long long start, elapsed;
    dict *dict = dictCreate(&BenchmarkDictType);
    long count = 0;
    int accurate = (flags & REDIS_TEST_ACCURATE);

    if (argc == 4) {
        if (accurate) {
            count = 5000000;
        } else {
            count = strtol(argv[3],NULL,10);
        }
    } else {
        count = 5000;
    }

    start_benchmark();
    for (j = 0; j < count; j++) {
        int retval = dictAdd(dict,stringFromLongLong(j),(void*)j);
        assert(retval == DICT_OK);
    }
    end_benchmark("Inserting");
    assert((long)dictSize(dict) == count);

    /* Wait for rehashing. */
    while (dictIsRehashing(dict)) {
        dictRehashMilliseconds(dict,100);
    }

    start_benchmark();
    for (j = 0; j < count; j++) {
        char *key = stringFromLongLong(j);
        dictEntry *de = dictFind(dict,key);
        assert(de != NULL);
        zfree(key);
    }
    end_benchmark("Linear access of existing elements");

    start_benchmark();
    for (j = 0; j < count; j++) {
        char *key = stringFromLongLong(j);
        dictEntry *de = dictFind(dict,key);
        assert(de != NULL);
        zfree(key);
    }
    end_benchmark("Linear access of existing elements (2nd round)");

    start_benchmark();
    for (j = 0; j < count; j++) {
        char *key = stringFromLongLong(rand() % count);
        dictEntry *de = dictFind(dict,key);
        assert(de != NULL);
        zfree(key);
    }
    end_benchmark("Random access of existing elements");

    start_benchmark();
    for (j = 0; j < count; j++) {
        dictEntry *de = dictGetRandomKey(dict);
        assert(de != NULL);
    }
    end_benchmark("Accessing random keys");

    start_benchmark();
    for (j = 0; j < count; j++) {
        char *key = stringFromLongLong(rand() % count);
        key[0] = 'X';
        dictEntry *de = dictFind(dict,key);
        assert(de == NULL);
        zfree(key);
    }
    end_benchmark("Accessing missing");

    start_benchmark();
    for (j = 0; j < count; j++) {
        char *key = stringFromLongLong(j);
        int retval = dictDelete(dict,key);
        assert(retval == DICT_OK);
        key[0] += 17; /* Change first number to letter. */
        retval = dictAdd(dict,key,(void*)j);
        assert(retval == DICT_OK);
    }
    end_benchmark("Removing and adding");
    dictRelease(dict);
    return 0;
}
#endif
