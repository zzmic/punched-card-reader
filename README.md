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

- To list connected Arduino boards:
  ```bash
  make board-list
  ```
  Make sure to record the port of the connected Arduino® UNO R4 WiFi board (e.g., `/dev/ttyACM0` on Linux, `COM3` on Windows, or `/dev/cu.usbmodemXXXX` on macOS) for use with the `upload` commands.
- To update the local cache of available platforms and libraries:
  ```bash
  make core-update-index
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
  make compile-punched-card-reader
  ```
- To upload the compiled sketch `PunchedCardReader/PunchedCardReader.ino` to the connected Arduino® UNO R4 WiFi board:
  ```bash
  make upload-punched-card-reader PORT=<serial-port>
  ```
- To work with alternative sketches, supply the path to the sketch via the `FILE` variable:
  ```bash
  make compile FILE=PunchedCardReader/<sketch-name>.ino
  make upload FILE=PunchedCardReader/<sketch-name>.ino PORT=<serial-port>
  ```
- For help:
  ```bash
  make help
  ```

## Caveats
- Note that the `setup()` and `loop()` functions can only appear once per sketch. If addtional sketches are included, ensure that they do not redefine these functions to avoid compilation errors.

## References
- [Arduino CLI Documentation](https://arduino.github.io/arduino-cli/1.3/)
- [Arduino CLI Sketch Specification](https://arduino.github.io/arduino-cli/1.3/sketch-specification/)
- [Arduino Example: Blink](https://docs.arduino.cc/built-in-examples/basics/Blink/)
- [Arduino Example: Calibrate Sensor Input](https://docs.arduino.cc/built-in-examples/analog/Calibration/)

