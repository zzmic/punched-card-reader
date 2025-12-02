#ifndef TEST_UTILS_H
#define TEST_UTILS_H

bool evenLEDsOnCalled;
bool evenLEDsOffCalled;
bool oddLEDsOnCalled;
bool oddLEDsOffCalled;

FullPhotodiodeState pdState;

bool sendPunchReadingCalled;
PunchReading sentPunchReading;
FullCardProcState cpState;

bool sendColumnCalled;
uint16_t sentCol;
bool sendCardEndCalled;
StreamProcState spState;

bool sendByteCalled;
char sentByte;

void resetMockedInterfaceTracking();

PunchReading stringToPunchReading(char *str);

void printPunchReading(PunchReading punched);

void printSavedSensorVals(uint16_t *vals);

#endif // TEST_UTILS_H
