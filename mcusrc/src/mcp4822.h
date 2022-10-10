#ifndef __is__included__9e9c61d3_3e59_11ed_ac01_b499badf00a1
#define __is__included__9e9c61d3_3e59_11ed_ac01_b499badf00a1 1

#ifdef __cplusplus
	extern "C" {
#endif

#ifndef __is_in_module__142e0c51_431e_11ed_9e74_b499badf00a1
	extern uint16_t mcp4822_CurrentValues[2];
#endif

/*@
	requires \valid(&SREG) && \valid(&DDRD) && \valid(&PORTD) && \valid(&DDRB) && \valid(&SPCR) && \valid(&SPSR);

	assigns SREG;
	assigns DDRD, PORTD;
	assigns DDRB;
	assigns SPCR, SPSR;
	assigns PRR;

	ensures (DDRD & 0x0C) == 0x0C;
	ensures (PORTD & 0x0C) == 0x0C;
	ensures ((DDRB & 0x24) == 0x24) && ((DDRB & 0x10) == 0);
	ensures (SPCR = 0x40) && (SPSR == 0x01);
	ensures SREG == \old(SREG);
	ensures PRR & 0x04 == 0x00;
*/
void mcp4822Init();

/*@
	requires (channel == 1) || (channel == 0);
	requires (gain == 1) || (gain == 0);
	requires (enableOutput == true) || (enableOutput == false);
	requires (value > 0) && (value < 4096);

	assigns SPSR, SPCR, SPDR;
	assigns mcp4822_CurrentValues[0], mcp4822_CurrentValues[1];

	ensures mcp4822_CurrentValues[channel] == value;
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
