# punched-card-reader


## Compile and Upload Arduino Sketches using Arduino CLI (Optional)
To update the local cache of available platforms and libraries:
```bash
arduino-cli core update-index
```

To install the core for the Arduino UNO R4 Boards:
```bash
arduino-cli core install arduino:renesas_uno
```

To list installed cores:
```bash
arduino-cli core list
```

To compile the Arduino sketch located in the `PunchedCardReader` directory:
```bash
arduino-cli compile --fqbn arduino:renesas_uno PunchedCardReader/<sketch_name>.ino
```

To upload the compiled sketch to the connected Arduino UNO R4 board:
```bash
arduino-cli upload -p /dev/ttyACM0 --fqbn arduino:renesas_uno PunchedCardReader/<sketch_name>.ino
```

## References
- Arduino CLI Documentation: https://arduino.github.io/arduino-cli/1.3/
- Arduino CLI Sketch Specification: https://arduino.github.io/arduino-cli/1.3/sketch-specification/
