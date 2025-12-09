#ifndef STREAM_PROCESSOR_H
#define STREAM_PROCESSOR_H

#include "Arduino.h"
#include "stdint.h"

/**
 * Enumeration for the stream processor state.
 */
typedef enum {
  s_TEXT = 0,
  s_BINARY = 1,
} StreamProcessorState;

/**
 * Character used to represent an unknown or unrecognized character.
 */
const char c_UNKNOWN = 0xEF;

void initStreamProcessor();
void sendByte(char b);
void sendColumn(uint16_t col);
void sendCardEnd();

#endif // STREAM_PROCESSOR_H
