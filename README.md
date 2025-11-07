# punched-card-reader

## Overview
This project is an Arduino-based punched card reader that can read and interpret data from punched cards. It aims to motivate certain OS concepts by demonstrating how slow historical I/O devices operated.

## Hardware Requirements
- [Arduino® UNO R4 WiFi Board](https://store-usa.arduino.cc/products/uno-r4-wifi)

## Project Hierarchy
```
punched-card-reader/
|-- .github/                   # GitHub Actions configuration files.
|-- docs/                      # Documentation directory.
|   |-- project-proposal/      # Project proposal documents.
|   |-- tlaplus-specification/ # TLA+ specification files.
|-- PunchedCardReader/         # Arduino sketch directory.
|-- test/                      # Test scripts and related files.
|-- README.md                  # Project documentation.
```

## Compile and Upload Arduino Sketches with the Makefile
This repository includes a convenience `Makefile` that wraps the `arduino-cli` commands, given that you have the `arduino-cli` installed and the Arduino® UNO R4 WiFi board connected to your local machine.
By default it targets the Arduino® UNO R4 WiFi board and the default sketch at `PunchedCardReader/PunchedCardReader.ino`.

- To update the local cache of available platforms and libraries:
  ```bash
  make core-update
  ```
- To install the core for the Arduino® UNO R4 WiFi board:
  ```bash
  make core-install
  ```
- To list installed/available cores:
  ```bash
  make core-list
  ```
- To compile the default sketch `PunchedCardReader/PunchedCardReader.ino`:
  ```bash
  make compile-punching-card-reader
  ```
- To upload the compiled sketch `PunchedCardReader/PunchedCardReader.ino` to the connected Arduino® UNO R4 WiFi board:
  ```bash
  make upload-punching-card-reader
  ```
- To work with alternative sketches, supply the path to the sketch via the `FILE` variable (e.g. `make compile FILE=PunchedCardReader/Blink.ino`):
  ```bash
  make compile FILE=PunchedCardReader/<sketch-name>.ino
  make upload FILE=PunchedCardReader/<sketch-name>.ino
  ```
- For help:
  ```bash
  make help
  ```

## References
- [Arduino CLI Documentation](https://arduino.github.io/arduino-cli/1.3/)
- [Arduino CLI Sketch Specification](https://arduino.github.io/arduino-cli/1.3/sketch-specification/)
- [Arduino Example: Blink](https://docs.arduino.cc/built-in-examples/basics/Blink/)
- [Arduino Example: Calibrate Sensor Input](https://docs.arduino.cc/built-in-examples/analog/Calibration/)

