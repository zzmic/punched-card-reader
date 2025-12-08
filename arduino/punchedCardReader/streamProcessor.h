#ifndef STREAM_PROCESSOR_H
#define STREAM_PROCESSOR_H

typedef enum {
  s_TEXT = 0,
  s_BINARY = 1,
} StreamProcState;

const char unknownChar = 0xEF;

void initStreamProcessor();

void sendColumn(uint16_t col);

void sendCardEnd();

#ifdef TESTING
char colToByte(uint16_t col);
//StreamProcState updateStreamProcState(StreamProcState curState, uint16_t col, bool cardEnded);
#endif // TESTING

#endif // STREAM_PROCESSOR_H
