/* 胡方凯 2000012155
    基于分离的双向链表的allocator
    分配块：header-prev-succ
    空闲块：header-prev-succ-footer
    使用first-fit策略
    链表是LIFO的
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  2048  /* Extend heap by this amount (bytes) */  
#define LISTSIZE 18
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PRE(p) (GET(p) & 0x2)    //已配的block使用prev位减少空间消耗                

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 


/* Global variables */
char *heap_listp = 0;  /* Pointer to first block */  

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Some functions I defined */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int get_list_entry(size_t asize)
{
    if (asize <= 24)
        return 0;
    else if (asize <= 48)
        return 1;
    else if (asize <= 72)
        return 2;
    else if (asize <= 96)
        return 3;
    else if (asize <= 120)
        return 4;
    else if (asize <= 240)
        return 5;
    else if (asize <= 480)
        return 6;
    else if (asize <= 960)
        return 7;
    else if (asize <= 1920)
        return 8;
    else if (asize <= 3840)
        return 9;
    else if (asize <= 7680)
        return 10;
    else if (asize <= 15360)
        return 11;
    else if (asize <= 30720)
        return 12;
    else if (asize <= 61440)
        return 13;
    else if (asize <= 122880)
        return 14;
    else if (asize <= 245760)
        return 15;
    else if (asize <= 491520)
        return 16;
    else
        return 17;
}


/*针对链表的操作和宏*/
static void insert(void *ptr);
static void delete(void *ptr);
/* 获取链表头的地址 */
#define GET_HEAD(n)    ((unsigned int)(GET(heap_listp + WSIZE * n)))

/* 获得空闲块的前后块的地址 */
#define GET_PREFB(bp)    ((unsigned int)(GET(bp)))
#define GET_SUCFB(bp)    ((unsigned int)(GET((char *)bp + WSIZE)))





/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    // printf("init..\n");
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((4+LISTSIZE)*WSIZE)) == (void *)-1) 
        return -1;

    /* Create the initial empty segrated list pointer */
    for (int i =0;i<LISTSIZE;i++){
        PUT(heap_listp + i*WSIZE, 0);
    }

    PUT(heap_listp + LISTSIZE*WSIZE, 0);          /* Alignment padding */
    PUT(heap_listp + ((1+LISTSIZE)*WSIZE), PACK(DSIZE, 0x3)); /* Prologue header */ 
    PUT(heap_listp + ((2+LISTSIZE)*WSIZE), PACK(DSIZE, 0x3)); /* Prologue footer */ 
    PUT(heap_listp + ((3+LISTSIZE)*WSIZE), PACK(0, 0x3));     /* Epilogue header */
    

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}




/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    // printf("malloc..\n");
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);                                 
    return bp;
} 

/* 
 * free - Free a block 
 */
void free(void *bp)
{
    // printf("free..\n");
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }
    //判断前面的位置是不是alloc，如果是alloc的话，空闲block也要加上
    size_t alloc = GET_PRE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, alloc));
    PUT(FTRP(bp), PACK(size, alloc));
    coalesce(bp);
}

/*
 * realloc - Naive implementation of realloc
    增加一步，判断能不能塞在老地方，不行的话再分配
 */
void *realloc(void *ptr, size_t size)
{
    // printf("realloc..\n");
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    size_t newsize = ALIGN(size + WSIZE);//多个4bytes的尾巴
    if(newsize < 32) newsize = 32;
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;

    if (oldsize >= newsize) //放得下直接放
    {

        place(ptr, newsize);
        return ptr;
    }
    else{ //放不下
        newptr = mm_malloc(size);
        /* If realloc() fails the original block is left untouched  */
        if(!newptr) {
            return 0;
        }
        /* Copy the old data. */
        memcpy(newptr, ptr, oldsize);

        /* Free the old block. */
        free(ptr);
        return newptr;
    }


}


/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    // printf("calloc..\n");
    size_t bytes = nmemb * size;
    void *newptr;
    /* just malloc some spaces and set them to zero */
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}



/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    // printf("extend..\n");
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    size_t alloc = GET_PRE(HDRP(bp));
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, alloc));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, alloc));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    // printf("coalesce..\n");
    size_t prev_alloc = GET_PRE(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {      /* Case 1 */
        //把后一个block的prev——alloc位置改成0，也就是最后3位只留下0x1
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0x1));
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, prev_alloc));
        PUT(FTRP(bp), PACK(size,prev_alloc));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        //现在的block要判断前前一个是不是pre——alloc的，用上一个block的pre——alloc位
        size_t prevprev_alloc = GET_PRE(FTRP(PREV_BLKP(bp)));
        
        delete(PREV_BLKP(bp));
        //把后一个block的prev——alloc位置改成0，也就是最后3位只留下0x1
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0x1));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, prevprev_alloc));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prevprev_alloc));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        //现在的block要判断前前一个是不是pre——alloc的，用上一个block的pre——alloc位
        size_t prevprev_alloc = GET_PRE(FTRP(PREV_BLKP(bp)));
        delete(NEXT_BLKP(bp));
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prevprev_alloc));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, prevprev_alloc));
        bp = PREV_BLKP(bp);
    }

    insert(bp);
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    // printf("place..\n");
    size_t csize = GET_SIZE(HDRP(bp));   
    size_t alloc = GET_PRE(HDRP(bp));
    delete(bp);

    if ((csize - asize) >= (2*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, alloc | 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0x2));
        PUT(FTRP(bp), PACK(csize-asize, 0x2));
        insert(bp);
    }
    else { 
        PUT(HDRP(bp), PACK(csize, alloc | 1));
        //后面的块要改prev——alloc位
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0x2 | next_alloc));
        if(!next_alloc)
            PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0x2 | next_alloc));
    }
}


/* 
 * find_fit - Find a fit for a block with asize bytes (using first fit)
 */
static void *find_fit(size_t asize)
{
    // printf("fit..\n");
    int entry = get_list_entry(asize);
    // printf("entry..\n");
    for( int i = entry ; i< LISTSIZE; i++){
        // printf(".\n");
        char* bp = GET_HEAD(i) + heap_listp;
        while(bp > heap_listp) {
            if(GET_SIZE(HDRP(bp)) >= asize){
                // printf("odk..\n");
                return (void *)bp;
            }
            /* 用后继找下一块 */
            bp = heap_listp + GET_SUCFB(bp);
        }
    }
    return NULL;
}


/*
 *  insert free block
 */
static void insert(void *bp)
{
    // printf("insert..\n");
    size_t size = GET_SIZE(HDRP(bp));
    /* 找到头节点位置 */
    int entry = get_list_entry(size);
    /* 空的 */
    if(GET_HEAD(entry) == 0){
        PUT(heap_listp + (WSIZE * entry), (unsigned int)((char*)bp - heap_listp));
        PUT(bp, 0);
        PUT((unsigned int *)bp + 1, 0);
    } 
    else {
        /* bp的succ放原来的第一个节点的offset */
        PUT(bp + WSIZE, GET_HEAD(entry));
        /* bp的prev没有（自己是第一个） */
        PUT(bp, 0);
        /* 之前节点的的prev放他离现在的节点的offset */
        PUT(heap_listp + GET_HEAD(entry),  (unsigned int)((char*)bp - heap_listp));
        /* 头节点放离第一个bp的offset */
        PUT(heap_listp + (WSIZE * entry),  (unsigned int)((char*)bp - heap_listp));
    }
}
/*
 *  delete acclocated block
 */
static void delete(void *bp)
{
    // printf("delete..\n");
    size_t size = GET_SIZE(HDRP(bp));
    /* 找到头节点位置 */
    int entry = get_list_entry(size);
    /* 唯一节点 */
    if(!GET_PREFB(bp)  && !GET_SUCFB(bp) ){
        PUT(heap_listp + WSIZE * entry, 0);
    } 
    /*头节点*/
    else if (!GET_PREFB(bp) && GET_SUCFB(bp)) 
    {
        PUT(heap_listp + WSIZE * entry, GET_SUCFB(bp));
        PUT(heap_listp+GET_SUCFB(bp), 0);
    }
    /*尾节点*/
    else if (GET_PREFB(bp) && !GET_SUCFB(bp)) 
    {
        PUT(heap_listp + WSIZE * entry, GET_SUCFB(bp));
        PUT(heap_listp + GET_PREFB(bp) + WSIZE, 0);
    }
    /*中间*/
    else if (GET_SUCFB(bp) && GET_PREFB(bp) ) {
        PUT(heap_listp+GET_PREFB(bp) + WSIZE, GET_SUCFB(bp));
        PUT(heap_listp+GET_SUCFB(bp), GET_PREFB(bp));
    }
}




/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}





void print_block();


/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno){
    char
     *ptr;
    //序言块
    ptr = heap_listp + ((1 + LISTSIZE ) * WSIZE);
    
    if (!in_heap(ptr) || (GET_SIZE(HDRP(ptr))) != DSIZE || !GET_ALLOC(HDRP(ptr))){
        printf("Prologue address = %p\n",ptr);
        printf("Prologue header = %p\n",GET(HDRP(ptr)));
    }

    //链表
    for(int i = 0; i < LISTSIZE; i++){
    {
        printf("class %d", i);
        ptr = heap_listp + GET_HEAD(i);
        while(ptr > heap_listp){            
            printf("address = %p\n",ptr);
            printf("header %p\n;", GET(HDRP(ptr)));
            printf("footer %p\n;", GET(FTRP(ptr)));
            printf("prev %p\n", heap_listp + GET_PREFB(ptr));     
            printf("next %p\n", heap_listp + GET_SUCFB(ptr));    
            ptr = heap_listp + GET_SUCFB(ptr);            
            }
        }
        printf("NULL\n");
    }
    //块
    for(ptr = heap_listp + ((2 +LISTSIZE) * LISTSIZE); GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)){
            printf("address = %p\n",ptr);
            printf("header %p\n;" ,GET(HDRP(ptr)));
            printf("footer %p\n\n;" ,GET(FTRP(ptr))); 
    }
}
