CPUFREQ=16000000L
FLASHDEV=/dev/ttyU0
FLASHBAUD=57600
#FLASHMETHOD=avrisp
#FLASHMETHOD=arduino
FLASHMETHOD=stk500
#MMCU=atmega328p
MMCU=atmega328

SRCFILES=src/main.c \
	src/sysclock.c \
	src/serial.c \
	src/adc.c \
	src/mcp4822.c
HEADFILES=src/main.h \
	src/sysclock.h \
	src/serial.h \
	src/adc.h \
	src/mcp4822.h

all: bin/controller.hex

bin/controller.bin: $(SRCFILES) $(HEADFILES)
	avr-gcc -Wall -Os -mmcu=$(MMCU) -DF_CPU=$(CPUFREQ) -o bin/controller.bin $(SRCFILES)

bin/controller.hex: bin/controller.bin

	avr-size -t bin/controller.bin
	avr-objcopy -j .text -j .data -O ihex bin/controller.bin bin/controller.hex

flash: bin/controller.hex

	sudo chmod 666 $(FLASHDEV)
ifeq ($(FLASHMETHOD),stk500)
	avrdude -v -p $(MMCU) -c $(FLASHMETHOD) -P $(FLASHDEV)  -U lfuse:w:0x7F:m -U flash:w:bin/controller.hex:i
	# Fuse 0x68
else
	avrdude -v -p $(MMCU) -c $(FLASHMETHOD) -P $(FLASHDEV) -b $(FLASHBAUD) -U lfuse:w:0x7F:m -U flash:w:bin/controller.hex:i
endif

framac: $(SRCFILES) $(HEADFILES)

	-rm framacreport.csv
	frama-c -wp-verbose 0 -wp -rte -wp-rte -wp-dynamic -wp-timeout 300 -cpp-extra-args="-I/usr/home/tsp/framaclib/  -DF_CPU=16000000L -D__AVR_ATmega2560__ -DFRAMAC_SKIP" $(SRCFILES) -then -no-unicode -report -report-csv framacreport.csv

framacgui: $(SRCFILE) $(HEADFILES)

	frama-c-gui -wp-verbose 0 -wp-rte -wp-dynamic -wp-timeout 300 -cpp-extra-args="-I/usr/home/tsp/framaclib/ -DF_CPU=16000000L -D__AVR_ATmega2560__ -DFRAMAC_SKIP"

clean:

	-rm *.bin
	-rm bin/*.bin

cleanall:

	-rm *.hex
	-rm bin/*hex

.PHONY: all clean cleanall flash
