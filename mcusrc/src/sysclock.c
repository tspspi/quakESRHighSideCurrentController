#include <avr/io.h>
#include <avr/interrupt.h>
#include <math.h>

#include "sysclock.h"

#ifdef __cplusplus
    extern "C" {
#endif

/*
    ================
    = System clock =
    ================
*/

#define SYSCLK_TIMER_OVERFLOW_MICROS                    (64L * 256L * (F_CPU / 1000000L))
#define SYSCLK_MILLI_INCREMENT                          (SYSCLK_TIMER_OVERFLOW_MICROS / 1000)
#define SYSCLK_MILLIFRACT_INCREMENT                     ((SYSCLK_TIMER_OVERFLOW_MICROS % 1000) >> 3)
#define SYSCLK_MILLIFRACT_MAXIMUM                       (1000 >> 3)

static volatile unsigned long int systemMillis                 = 0;
static volatile unsigned long int systemMilliFractional        = 0;
static volatile unsigned long int systemMonotonicOverflowCnt   = 0;
/*@
        axiomatic timerisr_has_valid_counters {
                axiom validMillis: (systemMillis >= 0) && (systemMillis < 4294967296);
                axiom validMillifracs: (systemMilliFractional >= 0) && (systemMilliFractional < 4294967296);
                axiom validOverflow: (systemMonotonicOverflowCnt >= 0) && (systemMonotonicOverflowCnt < 4294967296);
        }
*/

/*@
        requires (systemMillis >= 0) && (systemMillis < 4294967296);
        requires (systemMilliFractional >= 0) && (systemMilliFractional < 4294967296);
        requires (systemMonotonicOverflowCnt >= 0) && (systemMonotonicOverflowCnt < 4294967296);

        assigns systemMillis, systemMilliFractional, systemMonotonicOverflowCnt;

        ensures (systemMonotonicOverflowCnt == \old(systemMonotonicOverflowCnt)+1)
                || (systemMonotonicOverflowCnt == 0);

        ensures ((systemMillis == \old(systemMillis) + SYSCLK_MILLI_INCREMENT)
                && (systemMilliFractional == \old(systemMilliFractional + SYSCLK_MILLIFRACT_INCREMENT))
                && (\old(systemMilliFractional + SYSCLK_MILLIFRACT_INCREMENT < SYSCLK_MILLIFRACT_MAXIMUM)))
                ||
                ((systemMillis == \old(systemMillis) + SYSCLK_MILLI_INCREMENT + 1)
                && (systemMilliFractional == \old(systemMilliFractional + SYSCLK_MILLIFRACT_INCREMENT - SYSCLK_MILLIFRACT_MAXIMUM))
                && (\old(systemMilliFractional + SYSCLK_MILLIFRACT_INCREMENT >= SYSCLK_MILLIFRACT_MAXIMUM)));
*/
ISR(TIMER0_OVF_vect) {
        unsigned long int m, f;

        m = systemMillis;
        f = systemMilliFractional;

        m = m + SYSCLK_MILLI_INCREMENT;
        f = f + SYSCLK_MILLIFRACT_INCREMENT;

        if(f >= SYSCLK_MILLIFRACT_MAXIMUM) {
                f = f - SYSCLK_MILLIFRACT_MAXIMUM;
                m = m + 1;
        }

        systemMonotonicOverflowCnt = systemMonotonicOverflowCnt + 1;

        systemMillis = m;
        systemMilliFractional = f;
}

/*@
        assigns SREG;

        ensures (\result >= 0) && (\result < 4294967296);
        ensures SREG == \old(SREG);
*/
unsigned long int micros() {
        uint8_t srOld = SREG;
        unsigned long int overflowCounter;
        unsigned long int timerCounter;

        #ifndef FRAMAC_SKIP
                cli();
        #endif
        overflowCounter = systemMonotonicOverflowCnt;
        timerCounter = TCNT0;

        /*
                Check for pending overflow that has NOT been handeled up to now
        */
        if(((TIFR0 & 0x01) != 0) && (timerCounter < 255)) {
                overflowCounter = overflowCounter + 1;
        }

        SREG = srOld;

        return ((overflowCounter << 8) + timerCounter) * (64L / (F_CPU / 1000000L));
}

/*@
        requires millisecs > 0;

        assigns SREG;
*/
void delay(unsigned long millisecs) {
        unsigned int lastMicro, curMicro;
        /*
                Busy waiting the desired amount of milliseconds ... by
                polling mircos
        */
        lastMicro = (unsigned int)micros();
        //@ ghost int iterations = 0;
        /*@
                loop invariant millisecs >= 0;

                loop assigns SREG;
                loop assigns lastMicro, curMicro;

                loop variant millisecs - iterations;
        */
        while(millisecs > 0) {
                curMicro = micros();
                //@ ghost iterations = iterations + 1;
                if(curMicro - lastMicro >= 1000)  {
                        /* Every ~ thousand microseconds tick ... */
                        lastMicro = lastMicro + 1000;
                        millisecs = millisecs - 1;
                }
        }
        return;
}

/*@
        requires \valid(&TCCR0B) && \valid(&TCNT0) && \valid(&TCCR0A) && \valid(&TIFR0) && \valid(&TIMSK0) && \valid(&TCCR0B);
        requires \valid(&SREG);

        assigns TCCR0A;
        assigns TCNT0;
        assigns TCCR0A;
        assigns TIFR0;
        assigns TIMSK0;
        assigns TCCR0B;
        assigns SREG;

        assigns systemMillis, systemMilliFractional, systemMonotonicOverflowCnt;

        ensures TCCR0B == 0x00;
        ensures TCNT0  == 0x00;
        ensures TCCR0A == 0x00;
        ensures TIFR0  == 0x01;
        ensures TIMSK0 == 0x01;
        ensures TCCR0B == 0x03;
        ensures SREG == \old(SREG);

        ensures (systemMillis == 0) && (systemMilliFractional == 0) && (systemMonotonicOverflowCnt == 0);
*/
void sysclockInit() {
        uint8_t oldSr = SREG;
        #ifndef FRAMAC_SKIP
                cli();
        #endif

        systemMillis                 = 0;
        systemMilliFractional        = 0;
        systemMonotonicOverflowCnt   = 0;

        TCCR0B = 0x00;          /* Disable timer 0 */
        TCNT0  = 0x00;          /* Reset counter */

        TCCR0A = 0x00;
        TIFR0  = 0x01;          /* Clear overflow interrupt flag if triggered before */
        TIMSK0 = 0x01;          /* Enable overflow interrupt */
        TCCR0B = 0x03;          /* /64 prescaler */

        SREG = oldSr;
}

#ifdef __cplusplus
    } /* extern "C" { */
#endif
