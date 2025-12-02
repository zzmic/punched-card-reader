bool evenLEDsOnCalled;
bool evenLEDsOffCalled;
bool oddLEDsOnCalled;
bool oddLEDsOffCalled;

fullPhotodiodeState pdState;

bool sendPunchReadingCalled;
punchReading sentPunchReading;
fullCardProcState cpState;

bool sendColumnCalled;
uint16_t sentCol;
bool sendCardEndCalled;
streamProcState spState;

bool sendByteCalled;
char sentByte;

void resetMockedInterfaceTracking();

punchReading stringToPunchReading(char *str);

void printPunchReading(punchReading punched);

void printSavedSensorVals(uint16_t *vals);
