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
    "9조",
    /* First member's full name */
    "고병찬",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//워드 크기 4
#define WSIZE 4

//더블 워드 8
#define DSIZE 8

// 동적할당할 때 생성되는 배열의 크기가 chunk의 크기라고 생각하면 된다.
// CHUNKSIZE라는 이름을 4096이라는 상수로 정의하는 것과 같다.
// 프로그램이 메모리를 할당할 때, 한 번에 할당하는 기본 단위 크기가 4096바이트인 것이다.
// 초기 가용블록과 힙 확장을 위한 기본 크기
#define CHUNKSIZE (1<<12)

// x > y이면 x, 아니면 y
#define MAX(x,y) ((x) > (y)? (x):(y))

// PACK 매크로: 크기 size와 alloc 할당 비트를
// OR연산한 결과를 리턴
#define PACK(size,alloc) ((size) | (alloc))

// 인자인 주소 p가 참조하는 값을 리턴
#define GET(p) (*(unsigned int*)(p))

//p가 가리키는 값(워드)에 val로 값을 교체
#define PUT(p,val) (*(unsigned int *) (p)=(val))

// 0x7은 하위 비트 3개만 제거해서 블록 사이즈만 추출
#define GET_SIZE(p) (GET(p) & ~0x7)
// 0x1 하위 비트 1개로 0인지 1인지 구분
// 할당인지 가용인지 판단
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 header 위치 설정
#define HDRP(bp) ((char *) (bp) - WSIZE)
// 풋터 위치 설정
// bp는 헤더 바로 다음 위치.
// bp에서 출발. 헤더에 담긴 그 블록의 크기만큼 앞으로 갔다가
// 8만큼 뒤로 가면 FOOTER를 가리킴.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 포인터 반환
// 다음 블록의 header
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) -WSIZE)))
// 이전 블록의 포인터 반환
// 이전 블록의 FOOTER
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char* heap_listp;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // mem_sbrk를 통해 힙에 추가적인 메모리 공간을 할당 
    // (16바이트) 만약 실패하면 -1을 반환
    // 메모리 공간 할당해줘
    // 패딩, 프롤로그 header, FOOTER, 에필로그 header
    if((heap_listp=mem_sbrk(4*WSIZE))==(void *)-1){
        return -1;
    }

    // 패딩 역할(정렬 목적)
    PUT(heap_listp,0);
    // 프롤로그 header
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1)); 
    // 프롤로그 FOOTER
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1)); 
    // 에필로그 header
    PUT(heap_listp+(3*WSIZE),0);
    // 프롤로그 header와 FOOTER 사이로 설정
    heap_listp+=(2*WSIZE); 
    // 프롤로그가 initial block
    // initial 블록 사이로 heap_listp 이동

    // 처음으로 extend_heap 함수 호출
    // 인자는 4096/4 = 1024
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 조정된 블록 크기 실제로 할당된 블록의 크기
    size_t asize;
    // 힙이 부족할 경우 확장해야 할 크기
    size_t extendsize;
    char *bp;

    if (size==0){
        return NULL;
    }

    if (size<=DSIZE){
        // 최소 블록 크기 16바이트 할당
        asize=2*DSIZE;
    }else{
        // 8의 배수를 맞추기 위해 정렬
        asize=DSIZE*((size+DSIZE+(DSIZE-1))/DSIZE);
    }

    // find_fit으로 가용 블록을 찾고
    // 적절한 가용 블록이 있으면 place로 블록 할당
    if((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        return bp;
    }

    // 가용 블록이 없으면
    // extendsize를 할당하려는 블록 크기(asize)
    // 기본 확장 크기(chunksize)중 더 큰 값으로 설정한다.
    extendsize=MAX(asize,CHUNKSIZE);

    // 힙 확장
    if((bp=extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }

    // 확장된 블록에 대해 할당 완료
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp){
    // 헤더를 통해 블록 사이즈를 가져옴
    size_t size=GET_SIZE(HDRP(bp));

    // 헤더에 가용상태 0을 넣음
    PUT(HDRP(bp), PACK(size,0));
    // 풋터에 가용상태 0을 넣음
    PUT(FTRP(bp),PACK(size,0));
    // 해제한 블록을 인접한 가용 블록들과 병함
    coalesce(bp);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // realloc 을 할 수 없는 경우 밑에 if문 2가지 케이스
    if (size <= 0)
    {
        // 사이즈를 0으로 변경한 것은 free 한것과 동일함. 따라서 free 시켜준다.
        mm_free(ptr);
        return 0;
    }
    if (ptr == NULL)
    {
        // 애초에 크기를 조정할 블록이 존재하지 않았다. 그냥 할당한다 ( malloc )
        return mm_malloc(size);
    }
    // malloc 함수의 리턴값이 newp가 가리키는 주소임.
    void *newp = mm_malloc(size);
    // newp가 가리키는 주소가 NULL(할당되었다고 생각했지만 실패한 경우)
    if (newp == NULL)
    {
        return 0;
    }
    // 진짜 realloc 하는 코드임.
    size_t oldsize = GET_SIZE(HDRP(ptr));
    // ex int a(oldsize) = 10(GET_SIZE(HDRP(ptr));)
    // 그러므로 일단 여기까진 a = 10
    // 재할당이라는 것은 get_size 한 10값을 a(기존데이터주소)가 아닌 b(다른데이터주소)
    // 에 넣는다는 것이다.
    /*
    새로 할당하고자 하는 크기가 oldsize 보다 작으면
    그런데 oldsize가 가진 데이터의 크기가 size의 데이터 크기보다 크기때문에
    커서 전부 다 못들어간다. 그러면은 일단 size 만큼의 데이터만 size에 재할당하고
    나머지 부분(데이터)는 버린다. (가비지데이터)
    */
    if (size < oldsize)
    {
        oldsize = size; // oldsize의 데이터크기를 size 크기만큼 줄이겠다는 뜻.
    }
    // oldsize 데이터를  ptr(기존 주소) 에서 newp(새로 할당될 주소) 로 옮겨준다.
    memcpy(newp, ptr, oldsize);
    mm_free(ptr); // 원래 기존 주소에 있던 데이터를 free 시킨다.
    // 새로 할당된 데이터의 주소를 리턴한다.
    return newp;
}

//------------------------------------------------------

// extend_heap은 
// 1) 힙이 초기화될 때
// 2) mm_malloc이 적당한 맞춤 fit을 찾지 못했을때
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 워드가 짝수인 경우
    // WSIZE만큼 곱한 수가 size가 됨.
    size=(words%2) ? (words+1)*WSIZE: words*WSIZE;
    // mem_sbrk를 통해 힙 메모리 영역 할당 요청
    // mem_sbrk 함수가 메모리 할당을 실패할 경우
    // (void *)-1을 반환하는데, 숫자 -1과 비교할 수가 없기 때문에
    // long으로 자료형 변환을 해줘야함.
    if ((long) (bp=mem_sbrk(size))==-1){
        return NULL;
    }

    // header 설정 
    // 블록이 가용 상태
    PUT(HDRP(bp), PACK(size,0));
    
    // FOOTER 설정
    // 가용 상태
    PUT(FTRP(bp),PACK(size,0));
    
    //에필로그 header 설정. 1 할당된 상태 끝을 알리는
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    // 인접한 가용 블록들을 병합하는 함수
    // 메모리 할당의 단편화를 줄이고, 가용 블록의 크기 증가
    return coalesce(bp);
}



static void * coalesce(void *bp){

    // 이전 블록이 할당되었는지 확인
    size_t prev_alloc=GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 다음 블록이 할당되었는지 확인
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 자신 블록 사이즈
    size_t size=GET_SIZE(HDRP(bp));

    // case 1 (할당된 상태는 a, 가용 상태는 f로 표현)
    // 이전 블록 a
    // 다음 블록 a
    if (prev_alloc && next_alloc){
        return bp;
    }

    // 이전 블록 a
    // 다음 블록 f
    else if (prev_alloc && !next_alloc){
        // 다음 블록 전체 사이즈를 size에 더해줌
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        // header와 FOOTER에 0(가용 상태)
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }

    // 이전 블록 f
    // 다음 블록 a
    else if(!prev_alloc&&next_alloc){
        //이전 블록만큼 size 더해줌
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        // FOOTER, header에 가용
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        //블록 포인터를 이전 블록으로 옮김
        bp=PREV_BLKP(bp);
    }

    // 이전 블록 f
    // 다음 블록 f
    else{
        // 이전 블록과 다음 블록의 사이즈를 더해줌
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        // 이전 블록에 0 집어넣음
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        // 다음 블록에 0 집어넣음
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        // bp를 이전 블록으로 옮김
        bp=PREV_BLKP(bp);
    }
    return bp;
}

// 첫 번째 맞는 가용 블록
static void *find_fit(size_t asize){
    void *bp;
    // heap_listp 시작 부분부터 반복 시작
    // 힙 끝을 나타내는 에필로그 블록을 만날때까지 계속 탐색
    // 다음 블록으로 이동
    for (bp=heap_listp; GET_SIZE(HDRP(bp)) > 0; bp=NEXT_BLKP(bp)){
        // 현재 블록이 가용 상태인지 확인하고 아니면
        // 현재 블록에 할당 사이즈를 넣을 수 있는지 검사
        if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

//
static void place(void *bp,size_t asize){
    size_t csize=GET_SIZE(HDRP(bp));

    if((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));

        bp=NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }else{

        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}