#ifdef UNIT_TESTING

#ifndef UNIT_TESTS_H
#define UNIT_TESTS_H

typedef struct {
  uint8_t testNum;
  PhotodiodeDriverState startState;
  uint16_t readings[6];
  uint16_t offVals[12];
  uint16_t onVals[12];
  PhotodiodeDriverState endState;
  uint16_t offValsAfter[12];
  uint16_t onValsAfter[12];
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

// typedef struct {
//   uint8_t testNum;
//   StreamProcState startState;
//   uint16_t col;
//   bool cardEnded;
//   StreamProcState endState;
//   bool sendByteCalled;
//   char sentByte;
// } StreamProcTest;

typedef struct {
  uint16_t code;
  char expectedChar;
} EncodingTest;

void runUnitTests();

#endif // UNIT_TESTS_H

#endif // UNIT_TESTING
