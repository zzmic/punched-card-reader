#ifndef SOFTWARE_INTEGRATION_TESTS_H
#define SOFTWARE_INTEGRATION_TESTS_H

/**
 * Structure to hold integration test time step data.
 */
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

#endif SOFTWARE_INTEGRATION_TESTS_H
