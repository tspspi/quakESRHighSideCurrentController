#include <avr/io.h>
#include <avr/interrupt.h>
#include <math.h>

#include "main.h"
#include "mcp4822.h"

#ifdef __cplusplus
	extern "C" {
#endif

/*@
	requires \valid(&SPCR) && \valid(&SPSR) && \valid(&PORTD);

	assigns PORTD;
	assigns SPCR;
	assigns SPSR;

	ensures (PORTD & 0x80) == 0;
	ensures SPCR == 0x50;
	ensures SPSR == 0x01;
*/
static inline void mcp4822SPI_TransferBegin() {
	SPCR = 0x50 | 0x03;
	SPSR = 0x01;

	/* Chip select to low ... */
	PORTD = PORTD & (~(0x08));
}
/*@
	requires \valid(&SPCR) && \valid(&PORTD);

	assigns PORTD;
	assigns SPCR;

	ensures (PORTD & 0x80) == 0x80;
	ensures SPCR == 0x40;
*/
static inline void mcp4822SPI_TransferEnd() {
	SPCR = 0x40;
	PORTD = PORTD | 0x08;
}
/*@
	requires \valid(&SPDR) && \valid(&SPSR);

	assigns SPDR;

	ensures \result == SPDR;
*/
static inline uint8_t mcp4822SPI_Transfer(uint8_t byteOut) {
	SPDR = byteOut;
	asm volatile("nop");
	while((SPSR & 0x80) == 0) { }
	return SPDR;
}
/*@
	requires \valid(&PORTD);

	assigns PORTD;

	ensures (PORTD & 0x04) == 0x04;
*/
static inline void mcp4822SPI_LatchOutputs() {
	PORTD = PORTD & (~0x04);
	/* Two NOPs to reach 100 ns minimum time (at 16 MHz each is ~ 62 ns) */
	//@ assert (PORTD & 0x04) == 0;
	asm volatile("nop");
	asm volatile("nop");
	PORTD = PORTD | 0x04;
}

/*@
	requires \valid(&SREG) && \valid(&DDRD) && \valid(&PORTD) && \valid(&DDRB) && \valid(&SPCR) && \valid(&SPSR);

	assigns SREG;
	assigns DDRD, PORTD;
	assigns DDRB;
	assigns SPCR, SPSR;
	assigns PRR;

	ensures (DDRD & 0x0C) == 0x0C;
	ensures (PORTD & 0x0C) == 0x0C;
	ensures ((DDRB & 0x24) == 0x24) && ((DDRB & 0x80) == 0);
	ensures (SPCR = 0x40) && (SPSR == 0x01);
	ensures SREG == \old(SREG);
	ensures PRR & 0x04 == 0x00;
*/
void mcp4822Init() {
	uint8_t sregOld = SREG;
	#ifndef FRAMAC_SKIP
		cli();
	#endif

	/*
		Set I/O pins for SPI
			PD3 -> nCS
			PD2 -> nLDAC
			PB5 -> SCK
			PB3 -> SDI (MOSI)
			PB4 -> MISO

			PB2 is slave select, should be configured as output

		nCS -> output, high
		nLDAC -> output, high

	*/
	DDRD = DDRD | 0x0C;
	PORTD = PORTD | 0x0C;
	DDRB = (DDRB | 0x2C) & (~(0x10));
	PORTB = PORTB | 0x2C;

	/* Disable power saving mode ... */
	PRR = PRR & ~(0x04);

	/* SPI master mode, enable logic */
	SPCR = 0x40;
	SPSR = 0x01;

	SREG = sregOld;
}

/*@
	requires (channel == 1) || (channel == 0);
	requires (gain == 1) || (gain == 0);
	requires (enableOutput == true) || (enableOutput == false);
	requires (value > 0) && (value < 4096);
*/
void mcp4822SetOutput(
	uint8_t channel,
	uint8_t gain,
	bool enableOutput,
	uint16_t value
) {
	uint16_t msg = 0x00;

	/* Prepare message */
	msg = (value & 0x0FFF);
	if(channel != 0) {
		msg = msg | 0x8000;
	}
	if(gain != 0) {
		msg = msg | 0x2000;
	}
	if(enableOutput == true) {
		msg = msg | 0x1000;
	}

	/* Transmit 2 bytes ...*/
	mcp4822SPI_TransferBegin();
	mcp4822SPI_Transfer((uint8_t)((msg & 0xFF00) >> 8));
	mcp4822SPI_Transfer((uint8_t)(msg & 0x00FF));
	mcp4822SPI_TransferEnd();
	mcp4822SPI_LatchOutputs();
}

#ifdef __cplusplus
	} /* extern "C" { */
#endif
