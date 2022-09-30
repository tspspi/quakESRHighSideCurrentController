#include "main.h"
#include "sysclock.h"
#include "serial.h"
#include "adc.h"
#include "mcp4822.h"

#ifdef __cplusplus
    extern "C" {
#endif

/*@
	assigns SREG;
	assigns TCCR0A, TCNT0, TCCR0A, TIFR0, TIMSK0, TCCR0B;
	assigns 

*/
int main() {
	/*
		Initialize controller and hardware:

		Initialize ports and GPIOs -> ADC missing
		Initialize clocking module -> ok
		SPI für DAC (?) -> ok
		Set DAC value to zero, disable channel 2 -> ok
		Initialize ADC -> ok
		Initiale USART -> ok
	*/
	CLKPR = 0x80;
	CLKPR = 0;

	sysclockInit();
	serialInit();
	adcInit();
	mcp4822Init();
	mcp4822SetOutput(0, 0, true, 0);
	mcp4822SetOutput(1, 0, false, 0);
	sei();

	/* Endless loop ... */
	for(;;) {
		handleSerialMessages();
	}
}

#ifdef __cplusplus
    } /* extern "C" { */
#endif
