#ifndef UNIT_TESTS_H
#define UNIT_TESTS_H

typedef struct {
  uint8_t testNum;
  photodiodeDriverState startState;
  uint16_t readings[7];
  uint16_t offVals[13];
  uint16_t onVals[13];
  photodiodeDriverState endState;
  uint16_t offValsAfter[13];
  uint16_t onValsAfter[13];
  bool evenLEDsOnCalled;
  bool evenLEDsOffCalled;
  bool oddLEDsOnCalled;
  bool oddLEDsOffCalled;
  bool sendPunchReadingCalled;
  punchReading sentPunchReading;
} photodiodeTest;

typedef struct {
  uint8_t testNum;
  cardProcState startState;
  char *prevPunched;
  char *punched;
  cardProcState endState;
  char *prevPunchedAfter;
  bool sendColumnCalled;
  uint16_t sentCol;
  bool sendCardEndCalled;
} cardProcTest;

typedef struct {
  uint8_t testNum;
  streamProcState startState;
  uint16_t col;
  bool cardEnded;
  streamProcState endState;
  bool sendByteCalled;
  char sentByte;
} streamProcTest;

void runUnitTests();

#endif // UNIT_TESTS_H
