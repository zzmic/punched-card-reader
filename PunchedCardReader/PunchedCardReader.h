#ifndef PUNCHED_CARD_READER_H
#define PUNCHED_CARD_READER_H

#include "Arduino.h"
#include "CardProcessor.h"

// These don't include the card detector pin
#define READ_PINS_COUNT 6
#define EMITTER_PINS_COUNT 12

#define writePins(start_addr, end_addr, value) \
  for (const int *pin = start_addr; pin != end_addr; pin++) digitalWrite(*pin, value);

#define readPins(start_addr, end_addr, buffer) \
  for (const int *pin = start_addr; pin != end_addr; pin++) \
    { int *index = buffer; *index = analogRead(*pin); index++; }

#define printPins(start_addr, end_addr, buffer) \
  for (const int *pin = start_addr; pin != end_addr; pin++) \
    { int *index = buffer; Serial.print(analogRead(*pin)); Serial.print(":"); index++; } \
    Serial.println();

// P102
// D13 on the Arduino
const int c_READ_READY_PORT = 1;
const int c_READ_READY_PIN = 2;

const int c_ARDUINO_READ_READY_PIN = D13;

// Card detector pin
const int c_READ_READY_EMITTER_PIN = D12;

// As defined by our latest pins schema
const int c_ANALOG_PINS[6] = { A0, A1, A2, A3, A4, A5 };
const int c_DIGITAL_PINS[12] = { D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11 };

int readings_buffer[12] = { 1023 };

#endif