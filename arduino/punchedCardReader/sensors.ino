/**
 * Write a value to a range of pins.
 *
 * @param start_addr Pointer to the start of the pin array.
 * @param end_addr Pointer to the end of the pin array.
 * @param value The value to write to each pin.
 */
void writePins(const int *start_addr, const int *end_addr, int value) {
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    digitalWrite(*pin, value);
  }
}

/**
 * Read values from a range of pins into a buffer.
 *
 * @param start_addr Pointer to the start of the pin array.
 * @param end_addr Pointer to the end of the pin array.
 * @param buffer Pointer to the buffer where readings will be stored.
 */
void readPins(const int *start_addr, const int *end_addr, int *buffer) {
  int *index = buffer;
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    *index++ = analogRead(*pin);
  }
}

/**
 * Print pin readings from a range of pins.
 *
 * @param start_addr Pointer to the start of the pin array.
 * @param end_addr Pointer to the end of the pin array.
 */
void printPins(const int *start_addr, const int *end_addr, int * /*buffer*/) {
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    Serial.print(analogRead(*pin));
    Serial.print(":");
  }
  Serial.println();
}

/**
 * Print the contents of a buffer.
 *
 * @param start_addr Pointer to the start of the buffer.
 * @param size Number of elements in the buffer.
 */
void printBuffer(const int *start_addr, size_t size) {
  for (const int *item = start_addr; item != start_addr + size; ++item) {
    Serial.print(*item);
    Serial.print(":");
  }
  Serial.println();
}

/**
 * Initialize sensor pins.
 */
void initSensors() {
  for (int i = 0; i < EMITTER_PINS_COUNT; ++i) {
    pinMode(c_DIGITAL_PINS[i], OUTPUT);
  }

  for (int i = 0; i < READ_PINS_COUNT; ++i) {
    pinMode(c_DIGITAL_PINS[i], OUTPUT);
  }
}

#ifndef SOFTWARE_INTEGRATION_TESTING
/**
 * Read sensor values and return a `SensorReading` struct.
 *
 * @return SensorReading containing the readings from the sensors.
 */
SensorReading readSensors() {
  SensorReading result;
  for (int i = 0; i < READ_PINS_COUNT; i++) {
    result.readings[i] = analogRead(c_ANALOG_PINS[i]);
  }
  return result;
}
#endif // SOFTWARE_INTEGRATION_TESTING

#ifndef TESTING
/**
 * Turn on even LEDs.
 */
void evenLEDsOn() {
  writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, HIGH);
}

/**
 * Turn off even LEDs.
 */
void evenLEDsOff() {
  writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, LOW);
}

/**
 * Turn on odd LEDs.
 */
void oddLEDsOn() {
  writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, HIGH);
}

/**
 * Turn off odd LEDs.
 */
void oddLEDsOff() {
  writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, LOW);
}
#endif // TESTING
