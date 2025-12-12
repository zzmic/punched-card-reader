void printPunchReading(PunchReading& punched);
#ifdef TESTING

#ifndef TEST_UTILS_H
#define TEST_UTILS_H

/**
 * Variables for tracking calls to the mocked LED interface functions.
 */
bool evenLEDsOnCalled;
bool evenLEDsOffCalled;
bool oddLEDsOnCalled;
bool oddLEDsOffCalled;

/**
 * Photodiode state for testing.
 */
FullPhotodiodeState pdState;

/**
 * Variables for tracking calls to the mocked stream processor interface functions.
 */
bool sendPunchReadingCalled;
PunchReading sentPunchReading;
FullCardProcState cpState;

/**
 * Variables for tracking calls to the mocked stream processor interface functions.
 */
bool sendColumnCalled;
uint16_t sentCol;
bool sendCardEndCalled;
StreamProcState spState;

/**
 * Variables for tracking calls to the mocked serial interface functions.
 */
bool sendByteCalled;
char sentByte;

void resetMockedInterfaceTracking();

PunchReading stringToPunchReading(char *str);

void printSavedSensorVals(uint16_t *vals);

#endif // TEST_UTILS_H

#endif // TESTING
