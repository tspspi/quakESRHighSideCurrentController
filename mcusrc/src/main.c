#include "main.h"
#include "sysclock.h"
#include "serial.h"
#include "adc.h"

#ifdef __cplusplus
    extern "C" {
#endif

/*@
	assigns SREG;
	assigns TCCR0A, TCNT0, TCCR0A, TIFR0, TIMSK0, TCCR0B;


*/
int main() {
	/*
		Initialize controller and hardware:

		Initialize ports and GPIOs
		Initialize clocking module -> ok
		SPI für DAC
		Set DAC value to zero
		Initialize ADC -> ok
		Initiale USART -> ok
	*/
	sysclockInit();
	serialInit();
	adcInit();

	/* Endless loop ... */
	for(;;) {

	}
}

#ifdef __cplusplus
    } /* extern "C" { */
#endif
