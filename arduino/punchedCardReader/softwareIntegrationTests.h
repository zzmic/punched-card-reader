#ifdef SOFTWARE_INTEGRATION_TESTING

#ifndef SOFTWARE_INTEGRATION_TESTS_H
#define SOFTWARE_INTEGRATION_TESTS_H

typedef struct {
  uint8_t stepNum;
  uint16_t reading[6];

  bool evenLEDsOnCalled;
  bool evenLEDsOffCalled;
  bool oddLEDsOnCalled;
  bool oddLEDsOffCalled;

  bool sendPunchReadingCalled;
  PunchReading sentPunchReading;

  bool sendColumnCalled;
  uint16_t sentCol;
  bool sendCardEndCalled;

  bool sendByteCalled;
  char sentByte;
} IntegrationTestTimeStep;

bool checkMessages();

#endif // SOFTWARE_INTEGRATION_TESTS_H

#endif // SOFTWARE_INTEGRATION_TESTING
