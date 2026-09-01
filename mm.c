/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static char *heap_listp = NULL;
static char *rover = NULL;      /* 下次适配的起始查找位置 */
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);

/* single word (4) or double word (8) alignment */  //本章节假设单字为 4 字节，双字为 8 字节 
#define ALIGNMENT 8  //内存对齐

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) //向上取整至最接近的 ALIGNMENT 整数倍


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4           /* Word and header/footer size (bytes) */
#define DSIZE       8           /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12)     /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

void print_heap() {
    char *bp = heap_listp;
    printf("=== HEAP ===\n");
    int count = 0;
    while (GET_SIZE(HDRP(bp)) > 0) {
        size_t size = GET_SIZE(HDRP(bp));
        int alloc = GET_ALLOC(HDRP(bp));
        printf("block %d: bp=%p, size=%zu, alloc=%d\n", count, bp, size, alloc);
        bp = NEXT_BLKP(bp);
        count++;
        if (count > 100) { printf("too many blocks, stopping\n"); break; }
    }
    printf("end of heap\n");
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    char *new_bp = bp;

    if (prev_alloc && next_alloc) {
        /* Case 1: 前后都分配，不合并 */
        new_bp = bp;
        /* rover 不变 */
    } else if (prev_alloc && !next_alloc) {
        /* Case 2: 向后合并 */
        char *next = NEXT_BLKP(bp);        /* 必须在修改 bp 的 header 之前保存 */
        size += GET_SIZE(HDRP(next));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        new_bp = bp;
        if (rover == next) {               /* 用保存下来的地址比对 */
            rover = new_bp;
        }

    } else if (!prev_alloc && next_alloc) {
        /* Case 3: 向前合并 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        new_bp = PREV_BLKP(bp);
        if (rover == bp) {
            rover = new_bp;
        }
    } else {
        /* Case 4: 双向合并 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        new_bp = PREV_BLKP(bp);
        if (rover == bp || rover == NEXT_BLKP(bp) || rover == PREV_BLKP(bp)) {
            rover = new_bp;
        }
    }

    return new_bp;
}

static void *extend_heap(size_t words)
{

    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));          /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));          /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);

}


static void *find_fit(size_t asize){

    if (rover == NULL) rover = heap_listp;

    char *old_rover = rover;
    char *bp = rover;
    
    /* 从 rover 开始遍历 */
    for(; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){

        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            rover = bp;
            return bp;
        }

    }

    /* 从 rover 到结尾没找到，回绕到 heap_listp 重新找 */
    for(bp = heap_listp; bp != old_rover && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){

        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            rover = bp;
            return bp;
        }
        
    }

    /* 没找到 */
    return NULL;

    /* First-fit search 
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;   No fit */
}

static void place(void *bp, size_t asize){

    //printf("place: bp=%p, asize=%zu\n", bp, asize);
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (4 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        char *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK((csize - asize), 0));
        PUT(FTRP(next_bp), PACK((csize - asize), 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    //printf("place: bp=%p, asize=%zu\n", bp, asize);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;
    }

    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      /* Epilogue header */
    heap_listp += (2 * WSIZE);
    

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    rover = heap_listp;
    return 0;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if(size == 0){
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    
    asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);

    /* Search the free list for a fit */
    if((bp = find_fit(asize)) != NULL){
        //printf("find_fit returned bp=%p, asize=%zu\n", bp, asize);
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if(ptr == NULL){
        return;
    }

    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - 重新分配内存块
 *             如果 ptr == NULL，等同于 mm_malloc(size)
 *             如果 size == 0，等同于 mm_free(ptr) 并返回 NULL
 *             否则，尝试原地扩展；失败则搬移到新位置
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize;       /* 对齐后的块总大小（含头部+脚部） */
    size_t old_size;    /* 旧块总大小 */
    size_t remain;      /* 分割后的剩余空间 */
    char *new_ptr;      /* 搬移时的新块指针 */
    size_t copy_size;   /* 实际拷贝的字节数 */

    /* Case 1: ptr 为 NULL → 等同于 malloc */
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    /* Case 2: size 为 0 → 等同于 free */
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /*
     * 计算对齐后的块总大小（含头部+脚部）
     * 与 mm_malloc 保持完全一致
     */
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* 获取旧块的总大小（从头部读取） */
    old_size = GET_SIZE(HDRP(ptr));

    /* ============================================================
     * Case 3a: 收缩（新块大小 <= 旧块大小）
     * ============================================================ */
    if (asize <= old_size) {
        remain = old_size - asize;

        /* 若剩余空间 ≥ 最小块（16字节），分割出新的空闲块 */
        if (remain >= 4 * DSIZE) {
            /* 缩小当前块 */
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            /* 在紧邻的位置创建新的空闲块 */
            char *next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(remain, 0));
            PUT(FTRP(next_bp), PACK(remain, 0));

            /* 合并相邻空闲块（防御性） */
            coalesce(next_bp);
        }
        /* 若剩余空间 < 16 字节，直接吞噬（内部碎片） */
        return ptr;
    }

    /* ============================================================
     * Case 3b: 尝试原地扩展（新块大小 > 旧块大小）
     * ============================================================ */
    char *next_bp = NEXT_BLKP(ptr);
    int next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t next_size = GET_SIZE(HDRP(next_bp));
    size_t total_size = old_size + next_size;

    /* 条件：后继块为空闲 且 合并后的总大小 ≥ 请求大小 */
    if (!next_alloc && total_size >= asize) {

        if (rover == next_bp) {
            rover = ptr;
        }
        remain = total_size - asize;

        if (remain >= 4 * DSIZE) {
            /* 扩展当前块到 asize */
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            /* 在剩余空间创建新的空闲块 */
            char *new_free = NEXT_BLKP(ptr);
            PUT(HDRP(new_free), PACK(remain, 0));
            PUT(FTRP(new_free), PACK(remain, 0));

            /* 合并相邻空闲块 */
            coalesce(new_free);
        } else {
            /* 剩余空间太小，直接吞噬整个合并后的块 */
            PUT(HDRP(ptr), PACK(total_size, 1));
            PUT(FTRP(ptr), PACK(total_size, 1));
        }
        return ptr;
    }

    /* ============================================================
     * Case 3c: 无法原地扩展 → 搬移到新位置
     * ============================================================ */
    new_ptr = mm_malloc(size);
    if (new_ptr == NULL) {
        /* 标准 realloc：失败时旧块保持不变 */
        return NULL;
    }

    /* 拷贝旧块的有效载荷（取较小值） */
    copy_size = (old_size - DSIZE) < size ? (old_size - DSIZE) : size;
    memcpy(new_ptr, ptr, copy_size);

    /* 释放旧块 */
    mm_free(ptr);

    return new_ptr;
}














