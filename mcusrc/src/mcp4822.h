#ifndef __is__included__9e9c61d3_3e59_11ed_ac01_b499badf00a1
#define __is__included__9e9c61d3_3e59_11ed_ac01_b499badf00a1 1

#ifdef __cplusplus
	extern "C" {
#endif

/*@
	requires \valid(&SREG) && \valid(&DDRD) && \valid(&PORTD) && \valid(&DDRB) && \valid(&SPCR) && \valid(&SPSR);

	assigns SREG;
	assigns DDRD, PORTD;
	assigns DDRB;
	assigns SPCR, SPSR;

	ensures (DDRD & 0x0C) == 0x0C;
	ensures (PORTD & 0x0C) == 0x0C;
	ensures ((DDRB & 0x14) == 0x14) && ((DDRB & 0x80) == 0);
	ensures (SPCR = 0x40) && (SPSR == 0x01);
	ensures SREG == \old(SREG);
*/
void mcp4822Init();

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
);

#ifdef __cplusplus
	} /* extern "C" { */
#endif

#endif /* #ifndef __is__included__9e9c61d3_3e59_11ed_ac01_b499badf00a1 */
