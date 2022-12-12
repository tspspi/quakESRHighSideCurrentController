#include <avr/io.h>
#include <avr/interrupt.h>
#include <avr/eeprom.h>
#include <math.h>
#include <util/twi.h>
#include <stdint.h>

#define CURRENT_MEASURE_ADC 1

#include "./adc.h"
#include "./main.h"

#ifdef __cplusplus
    extern "C" {
#endif

uint16_t currentADC[ADCCOUNT];

static double adcCal_K, adcCal_D;
static uint16_t adcCalLow_Counts;
static uint16_t adcCalHigh_Counts;
static uint16_t adcCalHigh_Milliamps;

/*@
	requires \valid(&ADC) && \valid(&ADMUX);

	assigns currentADC[0 .. ADCCOUNT];
*/
ISR(ADC_vect) {
	uint8_t oldMUX = ADMUX;
    currentADC[(oldMUX + (ADCCOUNT-1)) % ADCCOUNT] = ADC;
    ADMUX = (((oldMUX & 0x1F) + 1) % ADCCOUNT) | (oldMUX & 0xE0);
}

struct eepromCalData {
    double adc0_K;
    double adc0_D;

    uint8_t chkSum;
};

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
    struct eepromCalData calData;

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

    /*
        Load calibration data (if exists)...
    */
    eeprom_read_block(&calData, EEPROM_ADCCALDATAOFFSET, sizeof(struct eepromCalData));
    uint8_t chkSum = 0;
    for(i = 0; i < sizeof(struct eepromCalData); i=i+1) {
        chkSum = chkSum ^ ((uint8_t*)(&calData))[i];
    }
    if(chkSum == 0) {
        adcCal_D = calData.adc0_D;
        adcCal_K = calData.adc0_K;
    } else {
        adcCal_D = 0;
        adcCal_K = 0.522448979592;
    }
}



uint16_t adcCountsToCurrentMA() {
    uint16_t a;
    /*
        Apply our calibration curve ... currently in code, this should be stored in EEPROM ...
    */
    uint8_t sregOld = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif
    a = currentADC[CURRENT_MEASURE_ADC];
    SREG = sregOld;

    return (uint16_t)(((double)(a) * adcCal_K) + adcCal_D);
}

static void adcRecalculateKD() {
    if((adcCalHigh_Counts == adcCalLow_Counts) || (adcCalLow_Counts > adcCalHigh_Counts)) {
        /* Use some sane default values ... */
        adcCal_D = 0;
        adcCal_K = 0.522448979592;
    } else {
        adcCal_K = ((double)adcCalHigh_Milliamps) / ((double)adcCalHigh_Counts - (double)adcCalLow_Counts);
        adcCal_D = -1.0 * adcCal_K * ((double)adcCalLow_Counts);
    }
}

void adcCalLow() {
    uint8_t sregOld = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif
    adcCalLow_Counts = currentADC[CURRENT_MEASURE_ADC];
    SREG = sregOld;

    adcRecalculateKD();
}

void adcCalHigh(uint16_t milliAmps) {
    uint8_t sregOld = SREG;
    #ifndef FRAMAC_SKIP
        cli();
    #endif
    adcCalHigh_Counts = currentADC[CURRENT_MEASURE_ADC];
    adcCalHigh_Milliamps = milliAmps;
    SREG = sregOld;

    adcRecalculateKD();
}

void adcCalStore() {
    struct eepromCalData calData;
    calData.adc0_D = adcCal_D;
    calData.adc0_K = adcCal_K;
    calData.chkSum = 0;

    uint8_t chkSum = 0x00;
    unsigned long int i;
    for(i = 0; i < sizeof(struct eepromCalData); i=i+1) {
        chkSum = chkSum ^ ((uint8_t*)(&calData))[i];
    }
    calData.chkSum = chkSum;

    eeprom_write_block(&calData, EEPROM_ADCCALDATAOFFSET, sizeof(struct eepromCalData));
}

double adcCalGet_K() { return adcCal_K; }
double adcCalGet_D() { return adcCal_D; }

#ifdef __cplusplus
    } /* extern "C" { */
#endif
