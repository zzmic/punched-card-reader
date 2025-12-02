#ifndef PHOTODIODE_DRIVER_H
#define PHOTODIODE_DRIVER_H

#include "Arduino.h"
#include "CardProcessor.h"
#include "stdint.h"

#define READ_PINS_COUNT 6
#define HALF_EMITTER_PINS_COUNT 6
#define EMITTER_PINS_COUNT 13

#define writePins(start_addr, end_addr, value) \
  for (const int *pin = start_addr; pin != end_addr; pin++) digitalWrite(*pin, value);

#define readPins(start_addr, end_addr, buffer) \
  for (const int *pin = start_addr; pin != end_addr; pin++) \
    { int *index = buffer; *index = analogRead(*pin); index++; }

#define printPins(start_addr, end_addr, buffer) \
  for (const int *pin = start_addr; pin != end_addr; pin++) \
    { int *index = buffer; Serial.print(analogRead(*pin)); Serial.print(":"); index++; } \
    Serial.println();

#define printBuffer(start_addr, size) \
  for (const int *item = start_addr; item != start_addr + size; item++) \
    { int val = *item; Serial.print(val); Serial.print(":"); } \
    Serial.println();

typedef enum {
  s_ALL_OFF = 0,
  s_EVEN_ON = 1,
  s_ODD_ON = 2,
  s_CALC = 3,
} PhotodiodeState;

typedef struct {
  PhotodiodeState state;
  int onVals[13];
  int offVals[13];
} PhotodiodeData;

typedef struct {
  int readings[7];
} SensorReadings;

// P102
// D13 on the Arduino
const int c_SENSE_PORT = 1;
const int c_SENSE_PIN = 2;

const int c_ARDUINO_SENSE_PIN = D13;

// Card detector pin
const int c_SENSE_EMITTER_PIN = D12;

// As defined by our latest pins schema
const int c_ANALOG_PINS[6] = { A0, A1, A2, A3, A4, A5 };
const int c_DIGITAL_PINS[13] = { D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, c_SENSE_EMITTER_PIN };
const int c_EVEN_PINS[6] = { D0, D2, D4, D6, D8, D10 };
const int c_ODD_PINS[6] = { D1, D3, D5, D7, D9, D11 };

const uint16_t c_MIN_DIFF = 700;

#define allLEDsOff() writePins(c_DIGITAL_PINS, c_DIGITAL_PINS + EMITTER_PINS_COUNT, LOW)
#define allLEDsOn() writePins(c_DIGITAL_PINS, c_DIGITAL_PINS + EMITTER_PINS_COUNT, HIGH)

#define evenLEDsOff() writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, LOW)
#define evenLEDsOn() writePins(c_EVEN_PINS, c_EVEN_PINS + HALF_EMITTER_PINS_COUNT, HIGH)

#define oddLEDsOff() writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, LOW)
#define oddLEDsOn() writePins(c_ODD_PINS, c_ODD_PINS + HALF_EMITTER_PINS_COUNT, HIGH)

PhotodiodeData CurrentState;

void initPhotodiodeDriver();
void sendSensorReading(SensorReadings readings);
void calibrate();

#ifdef defined(UNIT_TESTING_H) || defined(SOFTWARE_INTEGRATION_TESTING_H)
PhotodiodeData updatePhotodiodeData(PhotodiodeData current, SensorReadings readings);
#endif
#endif