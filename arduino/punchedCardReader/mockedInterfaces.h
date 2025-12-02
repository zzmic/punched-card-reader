extern bool evenLEDsOnCalled;
extern bool evenLEDsOffCalled;
extern bool oddLEDsOnCalled;
extern bool oddLEDsOffCalled;

extern fullPhotodiodeState pdState;

extern bool sendPunchReadingCalled;
extern punchReading sentPunchReading;
extern fullCardProcState cpState;

extern bool sendColumnCalled;
extern uint16_t sentCol;
extern bool sendCardEndCalled;
extern streamProcState spState;

extern bool sendByteCalled;
extern char sentByte;

void resetMockedInterfaceTracking();
