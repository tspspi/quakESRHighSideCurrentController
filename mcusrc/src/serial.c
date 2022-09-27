#include <avr/io.h>
#include <avr/interrupt.h>
#include <math.h>

#include "main.h"
#include "serial.h"
#include "adc.h"

#ifdef __cplusplus
    extern "C" {
#endif

#ifndef SERIAL_RINGBUFFER_SIZE
    #define SERIAL_RINGBUFFER_SIZE 1024
#endif

struct ringBuffer {
    volatile unsigned long int dwHead;
    volatile unsigned long int dwTail;

    volatile unsigned char buffer[SERIAL_RINGBUFFER_SIZE];
};

/*
    Ringbuffer utilis
*/
/*@
    predicate acsl_serialbuffer_valid(struct ringBuffer* lpBuf) =
        \valid(lpBuf)
        && \valid(&(lpBuf->dwHead))
        && \valid(&(lpBuf->dwTail))
        && (lpBuf->dwHead >= 0) && (lpBuf->dwHead < SERIAL_RINGBUFFER_SIZE)
        && (lpBuf->dwTail >= 0) && (lpBuf->dwTail < SERIAL_RINGBUFFER_SIZE);
*/
/*@
    requires lpBuf != NULL;
    requires \valid(lpBuf);
    requires \valid(&(lpBuf->dwHead));
    requires \valid(&(lpBuf->dwTail));

    assigns lpBuf->dwHead;
    assigns lpBuf->dwTail;
	assigns SREG;

    ensures lpBuf->dwHead == 0;
    ensures lpBuf->dwTail == 0;
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);
*/
static inline void ringBuffer_Init(volatile struct ringBuffer* lpBuf) {
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif
	lpBuf->dwHead = 0;
	lpBuf->dwTail = 0;
	SREG = oldSREG;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

    assigns SREG;

    ensures (\result == true) && (\result == false);
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);

    behavior isDataAvailable:
        assumes lpBuf->dwHead != lpBuf->dwTail;
        ensures \result == true;
    behavior noDataAvailable:
        assumes lpBuf->dwHead == lpBuf->dwTail;
        ensures \result == false;

    disjoint behaviors isDataAvailable, noDataAvailable;
    complete behaviors isDataAvailable, noDataAvailable;
*/
static inline bool ringBuffer_Available(volatile struct ringBuffer* lpBuf) {
    bool res;
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif
    res = (lpBuf->dwHead != lpBuf->dwTail) ? true : false;
	SREG = oldSREG;
    return res;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

    assigns SREG;

    ensures (\result == true) || (\result == false);
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);

    behavior noSpaceAvailable:
        assumes ((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) == lpBuf->dwTail;
        ensures \result == false;
    behavior spaceAvailable:
        assumes ((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) != lpBuf->dwTail;
        ensures \result == true;

    disjoint behaviors noSpaceAvailable, spaceAvailable;
    complete behaviors noSpaceAvailable, spaceAvailable;
*/
static inline bool ringBuffer_Writable(volatile struct ringBuffer* lpBuf) {
    bool res;
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif
    res = (((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) != lpBuf->dwTail) ? true : false;
	SREG = oldSREG;
    return res;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

    assigns SREG;

    ensures \result >= 0;
    ensures \result < SERIAL_RINGBUFFER_SIZE;
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);

    behavior noWrapping:
        assumes lpBuf->dwHead >= lpBuf->dwTail;
        ensures \result == (lpBuf->dwTail - lpBuf->dwHead);
    behavior wrapping:
        assumes lpBuf->dwHead < lpBuf->dwTail;
        ensures \result == (SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead;

    disjoint behaviors noWrapping, wrapping;
    complete behaviors noWrapping, wrapping;
*/
static inline unsigned long int ringBuffer_AvailableN(volatile struct ringBuffer* lpBuf) {
    unsigned long int res;
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(lpBuf->dwHead >= lpBuf->dwTail) {
        res = lpBuf->dwHead - lpBuf->dwTail;
    } else {
        res = (SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead;
    }

	SREG = oldSREG;
    return res;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

    assigns SREG;

    ensures \result >= 0;
    ensures \result < SERIAL_RINGBUFFER_SIZE;
    ensures acsl_serialbuffer_valid(lpBuf);

    behavior noWrapping:
        assumes lpBuf->dwHead >= lpBuf->dwTail;
        ensures \result == SERIAL_RINGBUFFER_SIZE - (lpBuf->dwTail - lpBuf->dwHead) - 1;
    behavior wrapping:
        assumes lpBuf->dwHead < lpBuf->dwTail;
        ensures \result == SERIAL_RINGBUFFER_SIZE - ((SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead) - 1;

    disjoint behaviors noWrapping, wrapping;
    complete behaviors noWrapping, wrapping;
*/
static inline unsigned long int ringBuffer_WriteableN(volatile struct ringBuffer* lpBuf) {
    return SERIAL_RINGBUFFER_SIZE - ringBuffer_AvailableN(lpBuf);
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

	assigns SREG;

    ensures (\result >= 0) && (\result <= 0xFF);
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);

    behavior emptyBuffer:
        assumes lpBuf->dwHead == lpBuf->dwTail;

        assigns \nothing;

        ensures \result == 0x00;
        ensures lpBuf->dwTail == \old(lpBuf->dwTail);
    behavior availableData:
        assumes lpBuf->dwHead != lpBuf->dwTail;

        assigns lpBuf->dwTail;

        ensures \result == lpBuf->buffer[\old(lpBuf->dwTail)];
        ensures lpBuf->dwTail == ((\old(lpBuf->dwTail)+1) % SERIAL_RINGBUFFER_SIZE);

    disjoint behaviors emptyBuffer, availableData;
    complete behaviors emptyBuffer, availableData;
*/
static unsigned char ringBuffer_ReadChar(volatile struct ringBuffer* lpBuf) {
    char t;

	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(lpBuf->dwHead == lpBuf->dwTail) {
        return 0x00;
    }

    t = lpBuf->buffer[lpBuf->dwTail];
    lpBuf->dwTail = (lpBuf->dwTail + 1) % SERIAL_RINGBUFFER_SIZE;

    SREG = oldSREG;

    return t;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);

    assigns SREG;

    ensures (\result >= 0) && (\result <= 0xFF);
    ensures acsl_serialbuffer_valid(lpBuf);
    ensures lpBuf->dwTail == \old(lpBuf->dwTail);
	ensures SREG == \old(SREG);

    behavior emptyBuffer:
        assumes lpBuf->dwHead == lpBuf->dwTail;
        assigns \nothing;
        ensures \result == 0x00;
    behavior availableData:
        assumes lpBuf->dwHead != lpBuf->dwTail;
        assigns \nothing;
        ensures \result == lpBuf->buffer[\old(lpBuf->dwTail)];

    disjoint behaviors emptyBuffer, availableData;
    complete behaviors emptyBuffer, availableData;
*/
static unsigned char ringBuffer_PeekChar(volatile struct ringBuffer* lpBuf) {
    unsigned char res = 0x00;

	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(lpBuf->dwHead != lpBuf->dwTail) {
        res = lpBuf->buffer[lpBuf->dwTail];
    }

    SREG = oldSREG;
    return res;
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);
    requires (dwDistance < SERIAL_RINGBUFFER_SIZE);

    assigns SREG;

    ensures (\result >= 0) && (\result <= 0xFF);
    ensures acsl_serialbuffer_valid(lpBuf);
    ensures lpBuf->dwTail == \old(lpBuf->dwTail);
	ensures SREG == \old(SREG);

    behavior emptyBuffer:
        assumes lpBuf->dwHead == lpBuf->dwTail;
        assigns SREG;
        ensures \result == 0x00;
    behavior distanceInRange:
        assumes ((lpBuf->dwHead > lpBuf->dwTail) && (dwDistance < (lpBuf->dwTail - lpBuf->dwHead))) || ((lpBuf->dwHead < lpBuf->dwTail) && (dwDistance < (SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead));
        assigns SREG;
        ensures \result == lpBuf->buffer[(\old(lpBuf->dwTail) + dwDistance) % SERIAL_RINGBUFFER_SIZE];
    behavior availableData:
        assumes ((lpBuf->dwHead > lpBuf->dwTail) && (dwDistance >= (lpBuf->dwTail - lpBuf->dwHead))) || ((lpBuf->dwHead < lpBuf->dwTail) && (dwDistance >= (SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead));
        assigns SREG;
        ensures \result == 0x00;

    disjoint behaviors emptyBuffer, distanceInRange, availableData;
    complete behaviors emptyBuffer, distanceInRange, availableData;
*/
static unsigned char ringBuffer_PeekCharN(
    volatile struct ringBuffer* lpBuf,
    unsigned long int dwDistance
) {
    unsigned char res = 0x00;

	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(lpBuf->dwHead != lpBuf->dwTail) {
        if(ringBuffer_AvailableN(lpBuf) > dwDistance) {
            res = lpBuf->buffer[(lpBuf->dwTail + dwDistance) % SERIAL_RINGBUFFER_SIZE];
        }
    }

    SREG = oldSREG;

    return res; 
}

/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);
    requires ((lpBuf->dwHead > lpBuf->dwTail) && (dwCount <= (lpBuf->dwTail - lpBuf->dwHead))) || ((lpBuf->dwHead < lpBuf->dwTail) && (dwCount <= (SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead));
    requires (dwCount >= 0);

    assigns lpBuf->dwTail;
	assigns SREG;

    ensures lpBuf->dwTail == ((\old(lpBuf->dwTail) + dwCount) % SERIAL_RINGBUFFER_SIZE);
    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);
*/
static inline void ringBuffer_discardN(
    volatile struct ringBuffer* lpBuf,
    unsigned long int dwCount
) {
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif
    lpBuf->dwTail = (lpBuf->dwTail + dwCount) % SERIAL_RINGBUFFER_SIZE;
	SREG = oldSREG;
    return;
}
/*
    required lpBuf != NULL;
    requires \valid(lpOut);
    requires \valid(&(lpOut[0..dwLen]));
    requires acsl_serialbuffer_valid(lpBuf);
    requires dwLen < SERIAL_RINGBUFFER_SIZE;

    assigns lpOut[0 .. dwLen-1];
	assigns SREG;

    ensures acsl_serialbuffer_valid(lpBuf);
    ensures (\result >= 0) && (\result <= dwLen);
	ensures SREG == \old(SREG);

    behavior notEnoughData:
        assumes ((dwLen > (lpBuf->dwTail - lpBuf->dwHead)) && (lpBuf->dwHead >= lpBuf->dwTail))
            || ((dwLen > ((SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead)) && (lpBuf->dwHead < lpBuf->dwTail));
        assigns SREG;
        ensures \result == 0
        
    behavior dataAvail:
        assumes ((dwLen <= (lpBuf->dwTail - lpBuf->dwHead)) && (lpBuf->dwHead >= lpBuf->dwTail))
            || ((dwLen <= ((SERIAL_RINGBUFFER_SIZE - lpBuf->dwTail) + lpBuf->dwHead)) && (lpBuf->dwHead < lpBuf->dwTail));

        assigns lpOut[0 .. dwLen-1];
		assigns SREG;

        ensures \result == dwLen;
        ensures \forall int i; 0 <= i < dwLen ==>
            lpOut[i] == lpBuf->buffer((\old(lpBuf->lpTail) + i) % SERIAL_RINGBUFFER_SIZE);
        ensures \lpBuf->lpTail == (\old(lpBuf->lpTail) + dwLen) % SERIAL_RINGBUFFER_SIZE;

    disjoint behaviors notEnoughData, dataAvail;
    complete behaviors notEnoughData, dataAvail;
*/
static unsigned long int ringBuffer_ReadChars(
    volatile struct ringBuffer* lpBuf,
    unsigned char* lpOut,
    unsigned long int dwLen
) {
    char t;
    unsigned long int i = 0;

	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(dwLen <= ringBuffer_AvailableN(lpBuf)) {
        /*@
            loop invariant 0 <= i <= dwLen;
            loop assigns lpOut[0 .. dwLen-1];
            loop variant dwLen - i;
        */
        for(i = 0; i < dwLen; i=i+1) {
            t = lpBuf->buffer[lpBuf->dwTail];
            lpBuf->dwTail = (lpBuf->dwTail + 1) % SERIAL_RINGBUFFER_SIZE;
            lpOut[i] = t;
        }
    }

    SREG = oldSREG;

    return i;
}
/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);
    requires (bData >= 0) && (bData <= 0xFF);

    assigns lpBuf->buffer[\old(lpBuf->dwHead)];
    assigns lpBuf->dwHead;
	assigns SREG;

    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);

    behavior bufferAvail:
        assumes ((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) != lpBuf->dwTail;
        assigns lpBuf->buffer[\old(lpBuf->dwHead)];
        assigns lpBuf->dwHead;
		assigns SREG;
        ensures lpBuf->buffer[lpBuf->dwHead] == bData;
        ensures lpBuf->dwHead == (\old(lpBuf->dwHead) + 1) % SERIAL_RINGBUFFER_SIZE;
    behavior bufferFull:
        assumes ((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) == lpBuf->dwTail;
        assigns SREG;

    disjoint behaviors bufferAvail, bufferFull;
    complete behaviors bufferAvail, bufferFull;
*/
static void ringBuffer_WriteChar(
    volatile struct ringBuffer* lpBuf,
    unsigned char bData
) {
	uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
	#endif

    if(((lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE) != lpBuf->dwTail) {
        lpBuf->buffer[lpBuf->dwHead] = bData;
        lpBuf->dwHead = (lpBuf->dwHead + 1) % SERIAL_RINGBUFFER_SIZE;
    }

    SREG = oldSREG;
}
/*@
    requires lpBuf != NULL;
    requires acsl_serialbuffer_valid(lpBuf);
    requires \valid(bData);
    requires \valid(&(bData[0 .. dwLen]));

    assigns lpBuf->buffer[0 .. SERIAL_RINGBUFFER_SIZE];
    assigns lpBuf->dwHead;
	assigns SREG;

    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);
*/
static void ringBuffer_WriteChars(
    volatile struct ringBuffer* lpBuf,
    unsigned char* bData,
    unsigned long int dwLen
) {
    unsigned long int i;

    /*@
        loop invariant 0 <= i < dwLen;

		loop assigns lpBuf->buffer[0 .. SERIAL_RINGBUFFER_SIZE];
		loop assigns lpBuf->dwHead;
		loop assigns SREG;

        loop variant dwLen - i;
    */
    for(i = 0; i < dwLen; i=i+1) {
        ringBuffer_WriteChar(lpBuf, bData[i]);
    }
}
/*@
    requires lpBuf != NULL;
    requires \valid(lpBuf);
    requires acsl_serialbuffer_valid(lpBuf);
    requires (ui >= 0) && (ui < 4294967297);

    assigns lpBuf->buffer[0 .. SERIAL_RINGBUFFER_SIZE];
    assigns lpBuf->dwHead;
	assigns SREG;

    ensures acsl_serialbuffer_valid(lpBuf);
	ensures SREG == \old(SREG);
*/
static void ringBuffer_WriteASCIIUnsignedInt(
    volatile struct ringBuffer* lpBuf,
    uint32_t ui
) {
    uint8_t i;
    char bTemp[10];
    uint8_t len;
    uint32_t current;

    /*
        We perform a simple conversion of the unsigned int
        and push all numbers into the ringbuffer
    */
    if(ui == 0) {
        ringBuffer_WriteChar(lpBuf, 0x30);
    } else {
        current = ui;
        len = 0;
        /*@
            loop invariant current >= 0;
            loop assigns bTemp[0 .. 9];
            loop assigns len;
            loop assigns current;
            loop variant current;
        */
        while(current != 0) {
            bTemp[len] = ((uint8_t)(current % 10)) + 0x30;
            len = len + 1;
            current = current / 10;
        }

        /*@
            loop invariant 0 <= i <= len;
            loop assigns lpBuf->buffer[0 .. SERIAL_RINGBUFFER_SIZE];
            loop variant len - i;
        */
        for(i = 0; i < len; i=i+1) {
            ringBuffer_WriteChar(lpBuf, bTemp[len - 1 - i]);
        }
    }
}

/*
	==================
	= Helper methods =
	==================
*/
/*@
    predicate acsl_is_whitespace(char c) =
        (c == 0x0A) || (c == 0x0D) || (c == 0x09) || (c == 0x0C) || (c == 0x0B) || (c == 0x20);
*/
/*@
    requires (c >= 0) && (c < 256);

    assigns \nothing;

    behavior ws:
        assumes acsl_is_whitespace(c);
        ensures \result == true;
    behavior nows:
        assumes !acsl_is_whitespace(c);
        ensures \result == false;

    disjoint behaviors ws, nows;
    complete behaviors ws, nows;
*/
static inline bool strIsWhite(char c) {
    switch(c) {
        case 0x0A:  return true;
        case 0x0D:  return true;
        case 0x09:  return true;
        case 0x0C:  return true;
        case 0x0B:  return true;
        case 0x20:  return true;
    }
    return false;
}
/*@
    requires (c >= 0) && (c < 256);

    assigns \nothing;

    behavior capitalLetter:
        assumes (c >= 0x41) && (c <= 0x5A);
        ensures \result == (c + 0x20);
    behavior nocapitalLetter:
        assumes (c < 0x41) || (c > 0x5A);
        ensures \result == c;

    disjoint behaviors capitalLetter, nocapitalLetter;
    complete behaviors capitalLetter, nocapitalLetter;
*/
static inline char strCasefoldIfChar(char c) {
    if((c >= 0x41) && (c <= 0x5A)) { c = c + 0x20; }
    return c;
}
/*@
    requires \valid(lpA) && \valid(lpB);
    requires \valid(&(lpA[0 .. dwLenA-1]));
    requires \valid(&(lpB[0 .. dwLenB-1]));

    assigns \nothing;

    behavior diffLen:
        assumes dwLenA != dwLenB;
        assigns \nothing;
        ensures \result == false;
    behavior equalString:
        assumes dwLenA == dwLenB;
        assumes \forall int i; 0 <= i < dwLenA ==>
            lpA[i] == lpB[i];
        assigns \nothing;
        ensures \result == true;
    behavior differentString:
        assumes dwLenA == dwLenB;
        assumes \exists int i; 0 <= i <= dwLenA
            && lpA[i] != lpB[i];
        assigns \nothing;
        ensures \result == false;

    disjoint behaviors diffLen, equalString, differentString;
    complete behaviors diffLen, equalString, differentString;
*/
static bool strCompare(
    char* lpA,
    unsigned long int dwLenA,
    unsigned char* lpB,
    unsigned long int dwLenB
) {
    unsigned long int i;

    if(dwLenA != dwLenB) { return false; }

    /*@
        loop invariant 0 <= i < dwLenA;
        loop assigns \nothing;
        loop variant dwLenA - i;
    */
    for(i = 0; i < dwLenA; i=i+1) {
        if(lpA[i] != lpB[i]) {
            return false;
        }
    }

    return true;
}
/*@
    requires \valid(lpA) && \valid(lpB);
    requires \valid(&(lpA[0 .. dwLenA-1]));
    requires \valid(&(lpB[0 .. dwLenB-1]));

    assigns \nothing;

    behavior atoolong:
        assumes dwLenA > dwLenB;
        assigns \nothing;
        ensures \result == false;
    behavior equalString:
        assumes dwLenA <= dwLenB;
        assumes \forall int i; 0 <= i < dwLenA ==>
            lpA[i] == lpB[i];
        assigns \nothing;
        ensures \result == true;
    behavior differentString:
        assumes dwLenA <= dwLenB;
        assumes \exists int i; 0 <= i <= dwLenA
            && lpA[i] != lpB[i];
        assigns \nothing;
        ensures \result == false;

    disjoint behaviors atoolong, equalString, differentString;
    complete behaviors atoolong, equalString, differentString;
*/
static bool strComparePrefix(
    char* lpA,
    unsigned long int dwLenA,
    unsigned char* lpB,
    unsigned long int dwLenB
) {
    unsigned long int i;

    if(dwLenA > dwLenB) { return false; }

    /*@
        loop invariant 0 <= i < dwLenA;
        loop assigns \nothing;
        loop variant dwLenA - i;
    */
    for(i = 0; i < dwLenA; i=i+1) {
        if(lpA[i] != lpB[i]) {
            return false;
        }
    }

    return true;
}
/*@
    requires \valid(lpStr);
    requires \valid(&(lpStr[0 .. dwLen-1]));

    assigns \nothing;

    ensures (\result >= 0) && (\result < 4294967296);
*/
static uint32_t strASCIIToDecimal(
    uint8_t* lpStr,
    unsigned long int dwLen
) {
    unsigned long int i;
    uint8_t currentChar;
    uint32_t currentValue = 0;

    /*@
        loop invariant 0 <= i < dwLen;
        loop assigns currentValue;
        loop variant dwLen - i;
    */
    for(i = 0; i < dwLen; i=i+1) {
        currentChar = lpStr[i];
        if((currentChar >= 0x30) && (currentChar <= 0x39)) {
            currentChar = currentChar - 0x30;
            currentValue = currentValue * 10 + currentChar;
        }
    }
    return currentValue;
}

/*
	================================================
	= Serial port initialization and configuration =
	================================================
*/
static volatile struct ringBuffer serialRB_TX;
static volatile struct ringBuffer serialRB_RX;

/*@
	requires \valid(&SREG) && \valid(&UBRR0) && \valid(&UCSR0A) && \valid(&UCSR0B) && \valid(&UCSR0C);

	assigns SREG;
	assigns UBRR0, UCSR0A, UCSR0B, UCSR0C;

	assigns serialRB_TX.dwHead, serialRB_TX.dwTail;
	assigns serialRB_RX.dwHead, serialRB_RX.dwTail;

	ensures (serialRB_TX.dwHead == 0) && (serialRB_TX.dwTail == 0);
	ensures (serialRB_RX.dwHead == 0) && (serialRB_RX.dwTail == 0);

	ensures UBRR0 == 103;
	ensures UCSR0A == 0x02;
	ensures UCSR0B == 0x90;
	ensures UCSR0C == 0x06;
	ensures SREG == \old(SREG);
*/
void serialInit() {
    uint8_t sregOld = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif

    ringBuffer_Init(&serialRB_TX);
    ringBuffer_Init(&serialRB_RX);

    UBRR0   = 103; // 16 : 115200, 103: 19200
    UCSR0A  = 0x02;
    UCSR0B  = 0x10 | 0x80; /* Enable receiver and RX interrupt */
    UCSR0C  = 0x06;

    SREG = sregOld;

    return;
}

/*@
	requires \valid(&UDR0);
	requires acsl_serialbuffer_valid(&serialRB_RX);

	assigns serialRB_RX.dwHead;
	assigns serialRB_RX.buffer[0 .. SERIAL_RINGBUFFER_SIZE];

	ensures acsl_serialbuffer_valid(&serialRB_RX);
*/
ISR(USART_RX_vect) {
    ringBuffer_WriteChar(&serialRB_RX, UDR0);
}

/*@
	requires \valid(&UDR0);
	requires \valid(&UCSR0B);
	requires acsl_serialbuffer_valid(&serialRB_RX);

	assigns serialRB_RX.dwTail;
	assigns UDR0;
	assigns UCSR0B;

	behavior dataAvailable:
		assumes serialRB_TX.dwHead != serialRB_TX.dwTail;

		assigns UDR0;
		assigns serialRB_TX.dwTail;

		ensures serialRB_TX.dwTail == (\old(serialRB_TX.dwTail) + 1) % SERIAL_RINGBUFFER_SIZE;
		ensures UDR0 == serialRB_TX.buffer[\old(serialRB_TX.dwTail)];
	behavior noDataAvailable:
		assumes serialRB_TX.dwHead == serialRB_TX.dwTail;

		assigns UDR0;
		assigns UCSR0B;

		ensures UDR0 == '$';
		ensures (UCSR0B & 0x28) == 0;

	complete behaviors noDataAvailable, dataAvailable;
	disjoint behaviors noDataAvailable, dataAvailable;
*/
ISR(USART_UDRE_vect) {
    if(ringBuffer_Available(&serialRB_TX) == true) {
        /* Shift next byte to the outside world ... */
        UDR0 = ringBuffer_ReadChar(&serialRB_TX);
    } else {
        /*
            Since no more data is available for shifting simply stop
            the transmitter and associated interrupts
        */
        UDR0 = '$';
        UCSR0B = UCSR0B & (~(0x08 | 0x20));
    }
}

/*@
	requires \valid(&SREG) && \valid(&UCSR0A) && \valid(&UCSR0B);

	assigns UCSR0A, UCSR0B, SREG;

	ensures ((UCSR0A) & 0x40) == 0x40;
	ensures ((UCSR0B) & 0x28) == 0x28;
	ensures SREG == \old(SREG);
*/
static void serialModeTX() {
    uint8_t sregOld = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif

    UCSR0A = UCSR0A | 0x40; /* Reset TXCn bit */
    UCSR0B = UCSR0B | 0x08 | 0x20;

    SREG = sregOld;
}

/*
    ================================================
    = Command handler for serial protocol on USART =
    ================================================

	Supported commands:
		$$$ID\n				Returns the controller ID
		$$$VER\n			Returns the controller version
		$$$SETA:XXX\n		Set the current for the filament (supplied in mA)
		$$$GETSETA\n		Returns the currently set filament current (in mA)
		$$$GETA\n			Returns the current measured
		$$$GETADC0\n		Returns the current read out value of ADC0 (filament current)

		$$$ADCCAL0\n		Sets the ADC zero calibration point. This will be used to
							calculate a base offset for the ADC
		$$$ADCCALH:XXX\n	Supplies the current "real" current. The system will sample
							the ADC and calculate the slope of the ADC
		$$$ADCCALSTORE\n	Stores the calibration values
		$$$ADCCALGET\n		Gets the current ADC calibration values

	Responses:
		$$$ID:[uuid of controller]\n	UUID of this controller board
		$$$VER:[version number]\n		Version of controller (monotonically incremented)
		$$$RSETA:XXX\n					Currently set filament current
		$$$RA:XXX\n						Measured filament current in mA
        $$$ADC0:XXX\n                   Raw value of ADC0
		$$$CALDATA:xxx:xxx\n			Offset and slope for calibration curve
		$$$ERR\n						Unknown command or processing error
*/

static unsigned char handleSerialMessages_StringBuffer[SERIAL_RINGBUFFER_SIZE];

static unsigned char handleSerialMessages_Response__ID[] = "$$$02fbc674-3e6a-11ed-ac01-b499badf00a1\n";
static unsigned char handleSerialMessages_Response__VER[] = "$$$0\n";
static unsigned char handleSerialMessages_Response__ERR[] = "$$$err\n";
static unsigned char handleSerialMessages_Response__ADC0_Part[] = "$$$adc0:";

/*@
	requires acsl_serialbuffer_valid(&serialRB_RX);
	requires dwLength > 5;

	assigns handleSerialMessages_StringBuffer[0 .. SERIAL_RINGBUFFER_SIZE];
	assigns SREG;
	assigns serialRB_RX.dwTail;

	ensures SREG == \old(SREG);
	ensures acsl_serialbuffer_valid(&serialRB_RX);
*/
static void handleSerialMessages_CompleteMessage(
    unsigned long int dwLength
) {
	/*
		Handle our message 
	*/
    unsigned long int dwLen;
    uint8_t sregOld;

    /*
        We have received a complete message - now we will remove the sync
        pattern, calculate actual length
    */
    ringBuffer_discardN(&serialRB_RX, 3); /* Skip sync pattern */
    dwLen = dwLength - 3;
    //@ assert dwLen > 2;

    /* Remove end of line for next parser ... */
    dwLen = dwLen - 1; /* Remove LF */
    //@ assert dwLen > 0;
    dwLen = dwLen - ((ringBuffer_PeekCharN(&serialRB_RX, dwLen-1) == 0x0D) ? 1 : 0); /* Remove CR if present */
    //@ assert dwLen >= 0;

    /* Now copy message into a local buffer to make parsing WAY easier ... */
    ringBuffer_ReadChars(&serialRB_RX, handleSerialMessages_StringBuffer, dwLen);
	//@ assert acsl_serialbuffer_valid(&serialRB_RX);

	if(strCompare("id", 2, handleSerialMessages_StringBuffer, dwLen) == true) {
		/* Send ID response ... */
        ringBuffer_WriteChars(&serialRB_TX, handleSerialMessages_Response__ID, sizeof(handleSerialMessages_Response__ID)-1);
        serialModeTX();
	} else if(strCompare("ver", 3, handleSerialMessages_StringBuffer, dwLen) == true) {
		ringBuffer_WriteChars(&serialRB_TX, handleSerialMessages_Response__VER, sizeof(handleSerialMessages_Response__VER)-1);
        serialModeTX();
	} else if(strComparePrefix("seta:", 5, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strCompare("getseta", 7, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strCompare("geta", 4, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strCompare("getadc0", 7, handleSerialMessages_StringBuffer, dwLen) == true) {
        uint16_t a;
        {
            sregOld = SREG;
            #ifndef FRAMAC_SKIP
                cli();
            #endif
            a = currentADC[0];
            SREG = sregOld;
            ringBuffer_WriteChars(&serialRB_TX, handleSerialMessages_Response__ADC0_Part, sizeof(handleSerialMessages_Response__ADC0_Part)-1);
            ringBuffer_WriteASCIIUnsignedInt(&serialRB_TX, a);
            ringBuffer_WriteChar(&serialRB_TX, 0x0A);
            serialModeTX();
        }

	} else if(strCompare("adccal0", 7, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strComparePrefix("adccalh:", 8, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strCompare("adccalstore", 11, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else if(strCompare("adccalget", 9, handleSerialMessages_StringBuffer, dwLen) == true) {

	} else {
		ringBuffer_WriteChars(&serialRB_TX, handleSerialMessages_Response__ERR, sizeof(handleSerialMessages_Response__ERR)-1);
        serialModeTX();
	}
}

/*@
	requires acsl_serialbuffer_valid(&serialRB_RX);

	assigns serialRB_RX.dwTail;
	assigns handleSerialMessages_StringBuffer[0 .. SERIAL_RINGBUFFER_SIZE];
	assigns SREG;

	ensures acsl_serialbuffer_valid(&serialRB_RX);
	ensures SREG == \old(SREG);
*/
void handleSerialMessages() {
    unsigned long int dwAvailableLength;
    unsigned long int dwMessageEnd;

    /*
        We simply check if a full message has arrived in the ringbuffer. If
        it has we will start to decode the message with the appropriate module
    */
    dwAvailableLength = ringBuffer_AvailableN(&serialRB_RX);
    if(dwAvailableLength < 3) { return; } /* We cannot even see a full synchronization pattern ... */
	//@ assert dwAvailableLength >= 3;

    /*
        First we scan for the synchronization pattern. If the first character
        is not found - skip over any additional bytes ...
    */
    /*@
        loop assigns serialRB_RX.dwTail;
    */
    while((ringBuffer_PeekChar(&serialRB_RX) != '$') && (ringBuffer_AvailableN(&serialRB_RX) > 3)) {
        ringBuffer_discardN(&serialRB_RX, 1); /* Skip next character */
    }

    /* If we are too short to fit the entire synchronization packet - wait for additional data to arrive */
    if(ringBuffer_AvailableN(&serialRB_RX) < 5) { return; }
	//@ assert dwAvailableLength >= 5;

    /*
        Discard additional bytes in case we don't see the full sync pattern and
        as long as data is available
    */
    /*@
        loop assigns serialRB_RX.dwTail;
    */
    while(
        (
            (ringBuffer_PeekCharN(&serialRB_RX, 0) != '$') ||
            (ringBuffer_PeekCharN(&serialRB_RX, 1) != '$') ||
            (ringBuffer_PeekCharN(&serialRB_RX, 2) != '$') ||
            (ringBuffer_PeekCharN(&serialRB_RX, 3) == '$')
        )
        && (ringBuffer_AvailableN(&serialRB_RX) > 4)
    ) {
        ringBuffer_discardN(&serialRB_RX, 1);
    }

    /*
        If there is not enough data for a potential packet to be finished
        leave (we still have the sync pattern at the start so we can simply
        retry when additional data has arrived)
    */
    if(ringBuffer_AvailableN(&serialRB_RX) < 5) { return; }
    dwAvailableLength = ringBuffer_AvailableN(&serialRB_RX);
	//@ assert dwAvailableLength >= 5;

    /*
        Now check if we have already received a complete message OR are seeing
        another more sync pattern - in the latter case we ignore any message ...
    */
    dwMessageEnd = 3;
    /*@
        loop assigns dwMessageEnd;
    */
    while((dwMessageEnd < dwAvailableLength) && (ringBuffer_PeekCharN(&serialRB_RX, dwMessageEnd) != 0x0A) && (ringBuffer_PeekCharN(&serialRB_RX, dwMessageEnd) != '$')) {
        dwMessageEnd = dwMessageEnd + 1;
    }
    if(dwMessageEnd >= dwAvailableLength) {
        return;
    }
	//@ assert dwMessageEnd < dwAvailableLength;

    if(ringBuffer_PeekCharN(&serialRB_RX, dwMessageEnd) == 0x0A) {
        /* Received full message ... */
        handleSerialMessages_CompleteMessage(dwMessageEnd+1);
    }
    if(ringBuffer_PeekCharN(&serialRB_RX, dwMessageEnd) == '$') {
        /* Discard the whole packet but keep the next sync pattern */
        ringBuffer_discardN(&serialRB_RX, dwMessageEnd);
    }

    /*
        In any other case ignore and continue without dropping the message ...
        we will wait till we received the whole message
    */
    return;
}

#ifdef __cplusplus
    } /* extern "C" { */
#endif
