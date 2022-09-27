#include <avr/io.h>
#include <avr/interrupt.h>
#include <math.h>
#include <util/twi.h>
#include <stdint.h>

#include "./adc.h"
#include "./main.h"

#ifdef __cplusplus
    extern "C" {
#endif

uint16_t currentADC[ADCCOUNT];

/*@
	requires \valid(&ADC) && \valid(&ADMUX);

	assigns currentADC[0 .. ADCCOUNT];
*/
ISR(ADC_vect) {
	uint8_t oldMUX = ADMUX;
    currentADC[(oldMUX + (ADCCOUNT-1)) % ADCCOUNT] = ADC;
    ADMUX = (((oldMUX & 0x1F) + 1) % ADCCOUNT) | (oldMUX & 0xE0);
}

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
void adcInit() {
    unsigned long int i;

    uint8_t oldSREG = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif

    for(i = 0; i < sizeof(currentADC) / sizeof(uint16_t); i=i+1) {
        currentADC[i] = ~0;
    }

    ADMUX = 0x40; /* AVCC reference voltage, MUX 0, right aligned */
    ADCSRB = 0x00; /* Free running trigger mode, highest mux bit 0 */
    ADCSRA = 0xBF; /* Prescaler / 128 -> about 1 kHz measurement interrupt enable; ADCs currently DISABLED */

    SREG = oldSREG;

    /* Launch ADC ... */
    ADCSRA = ADCSRA | 0x40; /* Start first conversion ... */
}


#ifdef __cplusplus
    } /* extern "C" { */
#endif
