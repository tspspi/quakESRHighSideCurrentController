#ifndef __is_included__193ed8fd_3e6c_11ed_ac01_b499badf00a1
#define __is_included__193ed8fd_3e6c_11ed_ac01_b499badf00a1 1

#ifndef ADCCOUNT
	#define ADCCOUNT 4
#endif

#ifdef __cplusplus
    extern "C" {
#endif

extern uint16_t currentADC[ADCCOUNT];

/*@
	requires \valid(&ADMUX) && \valid(&ADCSRB) && \valid(&ADCSRA) && \valid(&SREG);

    assigns ADMUX;
    assigns ADCSRB;
    assigns ADCSRA;
    assigns SREG;

    ensures (ADMUX == 0x40);
    ensures (ADCSRB == 0x00);
    ensures ADCSRA == 0xFF;
	ensures SREG == \old(SREG);
*/
void adcInit();

uint16_t adcCountsToCurrentMA();
void adcCalLow();
void adcCalHigh(uint16_t milliAmps);
void adcCalStore();

double adcCalGet_K();
double adcCalGet_D();


#ifdef __cplusplus
    } /* extern "C" { */
#endif

#endif /* #ifndef __is_included__193ed8fd_3e6c_11ed_ac01_b499badf00a1 */
