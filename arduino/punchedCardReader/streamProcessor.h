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
const char unknownChar = 0xEF;

void initStreamProcessor();

void sendColumn(uint16_t col);

void sendCardEnd();

#ifdef TESTING
char colToByte(uint16_t col);
//StreamProcState updateStreamProcState(StreamProcState curState, uint16_t col, bool cardEnded);
#endif // TESTING

#endif // STREAM_PROCESSOR_H
