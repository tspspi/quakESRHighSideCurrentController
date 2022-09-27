#ifndef __is_included__790c9d24_3e4e_11ed_ac01_b499badf00a1
#define __is_included__790c9d24_3e4e_11ed_ac01_b499badf00a1 

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

		axiom valid_UBBR: \valid(&UBRR0);
		axiom valid_UCSRA: \valid(&UCSR0A);
		axiom valid_UCSRB: \valid(&UCSR0B);
		axiom valid_UCSRC: \valid(&UCSR0C);
		axiom valid_UDR: \valid(&UDR0);

		axiom valid_ADMUX: \valid(&ADMUX);
		axiom valid_ADC: \valid(&ADC);
	}
*/

#ifdef __cplusplus
	extern "C" {
#endif

#ifndef __cplusplus
	#ifndef true
		#define true 1
		#define false 0
		typedef unsigned char bool;
	#endif
#endif





#ifdef __cplusplus
	}
#endif

#endif /* #ifndef __is_included__790c9d24_3e4e_11ed_ac01_b499badf00a1 */
