# punched-card-reader

## Overview
This project is an Arduino-based punched card reader that reads and interprets data from punched cards. It aims to motivate certain OS concepts by demonstrating how slow historical I/O devices operated.

## Hardware Requirements
- [Arduino® UNO R4 WiFi Board](https://store-usa.arduino.cc/products/uno-r4-wifi)

## Software Requirements
- [Arduino CLI](https://arduino.github.io/arduino-cli/1.3/installation/): A command-line interface for Arduino development.
- [Arm GNU Toolchain](https://developer.arm.com/Tools%20and%20Software/GNU%20Toolchain): A collection of tools for compiling and debugging ARM-based applications.
- [CppUTest](https://cpputest.github.io): A C/C++ unit testing framework.
- A GCC compiler that supports C++11 or later for building the simulation.

## Specifications
```
Punched Card Diameters
->  Length: 18.7325cm
->  Width: 8.255cm
->  Bits: 12 * 80 = 960b

Punched Card Reader:
->  Read start detected with an LED indicating presence of card
->  Notify card read start over serial
->  Starts with all LEDs off
->  Sampling Branch @ 1kHz:
  ->  Samples with LEDs off
  ->  Samples with LEDs on
  ->  Difference above a threshold comprises sample of either 1 or 0
->  Reads 12 bits no more than 80 times and emits at most 16-bit words over serial
->  Read end detected with an LED indicating absence of card
->  Notify card read end over serial
```

## CAD
We have created some preliminary CAD prototypes just to virtually explore the physical design of our system. These files, found in `.obj`, `.stl`, and `.f3z` formats, can be found in the respective folder according to their versions.

## Project Hierarchy
```
punched-card-reader/
|-- .github/                   # GitHub Actions configuration files.
|-- cad/                       # CAD files for the punched card reader
    |-- v1/                    # V1 prototype CAD files
|-- docs/                      # Documentation directory.
|   |-- tlaplus-specification/ # TLA+ specification files.
|-- PunchedCardReader/         # Arduino sketch directory.
    |-- test/                  # Test files for the Arduino sketch.
|-- sim/                       # Simulation files.
    |-- test/                  # Test files for the simulation.
|-- README.md                  # Project documentation.
```

## Build and Run the Punched Card Reader Simulation
The simulation of the punched card reader is implemented in C++ and can be built and run using the provided `Makefile`:
1. Run `make sim-build` to build the simulation.
2. Run `./sim/bin/main` to start the simulation in interactive mode (specify the `--binary` flag for binary output mode).
3. Insert a card file containing a $12$ (row) $\times$ $80$ (column) grid, where each entry represents a punch (any character) or no punch (`.`). Sample card files are available in the sim/test-cards/ directory.
4. To exit the simulation, type `done` when prompted for the next card file path.
5. Alternatively, do `make sim-test` to run the simulation on ALL the test cards in the sim/test-cards/ directory.

## Compile and Upload Arduino Sketches to the Arduino Board with the Makefile
This repository includes a convenience `Makefile` that wraps `arduino-cli` commands, assuming you have `arduino-cli` installed and the Arduino® UNO R4 WiFi board connected to your local machine. By default, it targets the Arduino® UNO R4 WiFi board and the default sketch at `PunchedCardReader/PunchedCardReader.ino`.

- To list connected Arduino boards:
  ```bash
  make arduino-board-list
  ```
  Make sure to record the port of the connected Arduino® UNO R4 WiFi board (e.g., `/dev/ttyACM0` on Linux, `COM3` on Windows, or `/dev/cu.usbmodemXXXX` on macOS) for use with the `upload` commands.
- To update the local cache of available platforms and libraries:
  ```bash
  make arduino-core-update-index
  ```
- To install the core for the Arduino® UNO R4 WiFi board:
  ```bash
  make arduino-core-install
  ```
- To list installed/available cores:
  ```bash
  make arduino-core-list
  ```
- To compile the default sketch `PunchedCardReader/PunchedCardReader.ino`:
  ```bash
  make arduino-compile-punched-card-reader
  ```
- To upload the compiled sketch `PunchedCardReader/PunchedCardReader.ino` to the connected Arduino® UNO R4 WiFi board:
  ```bash
  make arduino-upload-punched-card-reader PORT=<serial-port>
  ```
- To work with alternative sketches, supply the path to the sketch via the `FILE` variable:
  ```bash
  make arduino-compile FILE=PunchedCardReader/<sketch-name>.ino
  make arduino-upload FILE=PunchedCardReader/<sketch-name>.ino PORT=<serial-port>
  ```
- To display the help message:
  ```bash
  make help
  ```

## Run Unit Tests
Unit tests for the punched card reader can be found in the `test/` directory. The testing framework used is [CppUTest](https://github.com/cpputest/cpputest).

- ***TODO(zzmic):*** Add instructions for building and running the unit tests using Make.

## Caveats
- Note that the `setup()` and `loop()` functions can only appear once per sketch. If additional sketches are included, ensure that they do not redefine these functions to avoid compilation errors.

## Group Members
- Yi Lyo
- Patrick McCann
- Alexander Thaep
- Zhiwen "Michael" Zheng

## References
- [Arduino CLI Documentation](https://arduino.github.io/arduino-cli/1.3/)
- [Arduino Example: Blink](https://docs.arduino.cc/built-in-examples/basics/Blink/)
- [Arduino Example: Calibrate Sensor Input](https://docs.arduino.cc/built-in-examples/analog/Calibration/)
- [CppUTest](https://cpputest.github.io)
- [Arm GNU Toolchain](https://developer.arm.com/Tools%20and%20Software/GNU%20Toolchain)
- [Arm GNU Toolchain Downloads](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads)
- [gcc-arm-embedded — Homebrew Formulae](https://formulae.brew.sh/cask/gcc-arm-embedded)
- [Test Driving Arduino](https://christopherjmcclellan.wordpress.com/2018/02/16/test-driving-arduino/)
