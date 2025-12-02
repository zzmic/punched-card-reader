#ifndef PUNCHED_CARD_READER_H
#define PUNCHED_CARD_READER_H

#include "Arduino.h"
#include "CardProcessor.h"

int readings[13] = { 1023 };
bool data_leds[12] = { false };
bool sense_led = false;

#endif // PUNCHED_CARD_READER_H
