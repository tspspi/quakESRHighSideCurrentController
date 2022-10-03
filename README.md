# Simple 500 mA high voltage biasable current source

This project contains a simple OpAmp and MosFET based current supply
that can be controlled using a serial port. The whole project is built
around a ```IRF540N``` MosFET that's driven by an ```LM358``` in a way
to keep the voltage drop over a sense resistor constant - thus it provides
a somewhat controlable current source (note that there is no temperature
compensation but that was not necessary for this application).

The reference voltage is provided by an ```MCP4822``` SPI digital to analog
converter that's controlled by an ```ATMega328```. The serial port that's used
to control the current source is isolated using two ```PC816``` optocouplers - this
is necessary since the whole board will be biased to ```-2 kV``` with respect to the
controlling system. The load is powered by an 12V isolation transformer, the controller
uses the same power supply and derives it's 5V supply for DAC and microcontroller using
a simple ```LM317``` voltage regulator.

## The schematic

The schematic can be found in KiCAD format in the ```/kicad/currentcontroller``` directory

## Microcontroller firmware

The firmware for the microcontroller can be found in ```mcusrc``` and is built
using ```avr-gcc```. The firmware can be flashed by using the ```Makefile```:

```
make flash
```

The ACSL annotations are work in progress.

## Test script

To test the communication using a [simple serial TTL to USB converter](https://amzn.to/3C0tQMZ)
a simple Python library is available (currently no PyPi package) at ```mcusrc/sertest```