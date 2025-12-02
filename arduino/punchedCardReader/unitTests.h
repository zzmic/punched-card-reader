#ifndef UNIT_TESTS_H
#define UNIT_TESTS_H

typedef struct {
  uint8_t testNum;
  PhotodiodeDriverState startState;
  uint16_t readings[7];
  uint16_t offVals[13];
  uint16_t onVals[13];
  PhotodiodeDriverState endState;
  uint16_t offValsAfter[13];
  uint16_t onValsAfter[13];
  bool evenLEDsOnCalled;
  bool evenLEDsOffCalled;
  bool oddLEDsOnCalled;
  bool oddLEDsOffCalled;
  bool sendPunchReadingCalled;
  PunchReading sentPunchReading;
} PhotodiodeTest;

typedef struct {
  uint8_t testNum;
  CardProcState startState;
  char *prevPunched;
  char *punched;
  CardProcState endState;
  char *prevPunchedAfter;
  bool sendColumnCalled;
  uint16_t sentCol;
  bool sendCardEndCalled;
} CardProcTest;

typedef struct {
  uint8_t testNum;
  StreamProcState startState;
  uint16_t col;
  bool cardEnded;
  StreamProcState endState;
  bool sendByteCalled;
  char sentByte;
} StreamProcTest;

void runUnitTests();

#endif // UNIT_TESTS_H
