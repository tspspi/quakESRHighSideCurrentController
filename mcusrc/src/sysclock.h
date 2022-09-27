#include <avr/io.h>
#include <avr/interrupt.h>
#include <math.h>
#include <util/twi.h>

/*@
	axiomatic hardware_registers {
		axiom valid_SREG: \valid(&SREG);

		axiom valid_TCCR0A: \valid(&TCCR0A);
		axiom valid_TCCR0B: \valid(&TCCR0B);
		axiom valid_TIMSK0: \valid(&TIMSK0);
		axiom valid_TCNT0: \valid(&TCNT0);
		axiom valid_TIFR0: \valid(&TIFR0);

		axiom valid_PORTA: \valid(&PORTA);
		axiom valid_PORTB: \valid(&PORTB);
		axiom valid_PORTC: \valid(&PORTC);
		axiom valid_PORTD: \valid(&PORTD);

		axiom valid_DDRA: \valid(&DDRA);
		axiom valid_DDRB: \valid(&DDRB);
		axiom valid_DDRC: \valid(&DDRC);
		axiom valid_DDRD: \valid(&DDRD);
	}
*/

#ifndef __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1
#define __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1 1

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

        ensures TCCR0B == 0x00;
        ensures TCNT0  == 0x00;
        ensures TCCR0A == 0x00;
        ensures TIFR0  == 0x01;
        ensures TIMSK0 == 0x01;
        ensures TCCR0B == 0x03;
        ensures SREG == \old(SREG);
*/

void sysclockInit();

/*@
        assigns SREG;

        ensures (\result >= 0) && (\result < 4294967296);
        ensures SREG == \old(SREG);
*/
unsigned long int micros();

/*@
        requires millisecs > 0;

        assigns SREG;
*/
void delay(unsigned long millisecs);

#endif /* __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1 */
