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

void resetMockedInterfaceTracking() {
  evenLEDsOnCalled = false;
  evenLEDsOffCalled = false;
  oddLEDsOnCalled = false;
  oddLEDsOffCalled = false;

  sendPunchReadingCalled = false;

  sendColumnCalled = false;
  sendCardEndCalled = false;

  sendByteCalled = false;
}

#if defined(UNIT_TESTING) || defined(SOFTWARE_INTEGRATION_TESTING)
void evenLEDsOn() {
  evenLEDsOnCalled = true;
}

void evenLEDsOff() {
  evenLEDsOffCalled = true;
}

void oddLEDsOn() {
  oddLEDsOnCalled = true;
}

void oddLEDsOff() {
  oddLEDsOffCalled = true;
}

void sendSensorReading(sensorReading reading) {
  pdState = updatePhotodiodeState(pdState, reading);
}

void sendPunchReading(punchReading reading) {
  sendPunchReadingCalled = true;
  sentPunchReading = reading;

  #ifndef UNIT_TESTING
  cpState = updateCardProcState(cpState, reading);
  #endif
}

void sendColumn(uint16_t col) {
  sendColumnCalled = true;
  sentCol = col;

  #ifndef UNIT_TESTING
  spState = updateStreamProcState(spState, col, false);
  #endif
}

void sendCardEnd() {
  sendCardEndCalled = true;

  #ifndef UNIT_TESTING
  spState = updateStreamProcState(spState, 0, true);
  #endif
}

void sendByte(char c) {
  sendByteCalled = true;
  sentByte = c;
}
#endif
