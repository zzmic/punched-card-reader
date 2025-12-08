#ifdef TESTING

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

PunchReading stringToPunchReading(char *str) {
  PunchReading output;
  for (int i = 0; i < 12; i++) {
    if (str[i] == '1') {
      output.holes[i] = true;
    } else {
      output.holes[i] = false;
    }
  }
  return output;
}

void printPunchReading(PunchReading punched) {
  for (int i = 0; i < 12; i++) {
    if (punched.holes[i]) {
      Serial.print("1");
    } else {
      Serial.print("0");
    }
  }
}

void printSavedSensorVals(uint16_t *vals) {
  Serial.print("[");
  for (int i = 0; i < 12; i++) {
    Serial.print(vals[i]);
    Serial.print(", ");
  }
  Serial.print(vals[12]);
  Serial.print("]");
}

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

void sendSensorReading(SensorReading reading) {
  pdState = updatePhotodiodeState(pdState, reading);
}

void sendPunchReading(PunchReading reading) {
  sendPunchReadingCalled = true;
  sentPunchReading = reading;

  #ifndef UNIT_TESTING
  cpState = updateCardProcState(cpState, reading);
  #endif // UNIT_TESTING
}

void sendColumn(uint16_t col) {
  sendColumnCalled = true;
  sentCol = col;

  #ifndef UNIT_TESTING
  spState = updateStreamProcState(spState, col, false);
  #endif // UNIT_TESTING
}

void sendCardEnd() {
  sendCardEndCalled = true;

  #ifndef UNIT_TESTING
  spState = updateStreamProcState(spState, 0, true);
  #endif // UNIT_TESTING
}

void sendByte(char c) {
  sendByteCalled = true;
  sentByte = c;
}

#endif // TESTING
