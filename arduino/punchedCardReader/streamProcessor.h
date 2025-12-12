#ifndef STREAM_PROCESSOR_H
#define STREAM_PROCESSOR_H

/**
 * Enumeration for the stream processor state.
 */
typedef enum {
  s_TEXT = 0,
  s_BINARY = 1,
} StreamProcState;

/**
 * Character used to represent an unknown or unrecognized character.
 */
const char UNKNOWN_CHAR = 0xEF;

/**
 * Pattern representing a whitespace column in punched card encoding.
 */
const uint16_t WHITESPACE_COL = 0b000100000100;

void initStreamProcessor();

void sendColumn(uint16_t col);

void sendCardEnd();

#ifdef TESTING
char colToByte(uint16_t col);
#endif // TESTING

#endif // STREAM_PROCESSOR_H
