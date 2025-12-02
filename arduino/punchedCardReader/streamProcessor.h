typedef enum {
  s_TEXT = 0,
  s_BINARY = 1,
} streamProcState;

const char unknownChar = 0xEF;

void initStreamProcessor();

void sendColumn(uint16_t col);

void sendCardEnd();

#ifdef TESTING
streamProcState updateStreamProcState(streamProcState curState, uint16_t col, bool cardEnded);
#endif
