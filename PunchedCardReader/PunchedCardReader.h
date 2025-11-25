#ifndef PUNCHED_CARD_READER_H
#define PUNCHED_CARD_READER_H

#include "Arduino.h"

#define READ_PINS_COUNT 6
#define EMITTER_PINS_COUNT 12

// P102
const uint8_t READ_READY_PORT = 1;
const uint8_t READ_READY_PIN = 2;

const uint8_t READ_READY_EMITTER_PIN = D12;

const uint8_t ANALOG_PINS[6] = { A0, A1, A2, A3, A4, A5 };
const uint8_t DIGITAL_PINS[12] = { D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11 };

#endif