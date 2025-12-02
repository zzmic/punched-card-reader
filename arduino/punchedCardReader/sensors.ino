#include "sensors.h"

void writePins(const int *start_addr, const int *end_addr, int value) {
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    digitalWrite(*pin, value);
  }
}

void readPins(const int *start_addr, const int *end_addr, int *buffer) {
  int *index = buffer;
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    *index++ = analogRead(*pin);
  }
}

void printPins(const int *start_addr, const int *end_addr, int * /*buffer*/) {
  for (const int *pin = start_addr; pin != end_addr; ++pin) {
    Serial.print(analogRead(*pin));
    Serial.print(":");
  }
  Serial.println();
}

void printBuffer(const int *start_addr, size_t size) {
  for (const int *item = start_addr; item != start_addr + size; ++item) {
    Serial.print(*item);
    Serial.print(":");
  }
  Serial.println();
}

void initSensors() {
    for (int i = 0; i < EMITTER_PINS_COUNT; ++i) {
      pinMode(c_DIGITAL_PINS[i], OUTPUT);
    }
    pinMode(c_SENSE_EMITTER_PIN, INPUT);
    writePins(c_DIGITAL_PINS, c_DIGITAL_PINS + EMITTER_PINS_COUNT, HIGH);
}

#ifndef SOFTWARE_INTEGRATION_TESTING
SensorReading readSensors() {
  SensorReading result;
  readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT,
           (int *)result.readings);
  result.readings[6] = (uint16_t)digitalRead(c_SENSE_EMITTER_PIN);
  return result;
}
#endif // SOFTWARE_INTEGRATION_TESTING

#ifndef TESTING
void evenLEDsOn() {
  writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, LOW);
}

void evenLEDsOff() {
  writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, HIGH);
}

void oddLEDsOn() {
  writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, HIGH);
}

void oddLEDsOff() {
  writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, LOW);
}
#endif // TESTING
