#ifndef SOFTWARE_INTEGRATION_TESTS_H
#define SOFTWARE_INTEGRATION_TESTS_H

typedef struct {
  uint8_t stepNum;
  uint16_t reading[7];

  bool evenLEDsOnCalled;
  bool evenLEDsOffCalled;
  bool oddLEDsOnCalled;
  bool oddLEDsOffCalled;

  bool sendPunchReadingCalled;
  punchReading sentPunchReading;

  bool sendColumnCalled;
  uint16_t sentCol;
  bool sendCardEndCalled;

  bool sendByteCalled;
  char sentByte;
} integrationTestTimeStep;

bool checkMessages();

#endif // SOFTWARE_INTEGRATION_TESTS_H
