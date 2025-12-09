/**
 * Print a `PunchReading` struct as a string of '1's and '0's.
 *
 * @param punched The PunchReading struct to print.
 */
void printPunchReading(PunchReading punched) {
  for (int i = 0; i < 12; i++) {
    if (punched.holes[i]) {
      Serial.print("1");
    } else {
      Serial.print("0");
    }
  }
}

#ifdef TESTING

/**
 * Reset all tracking variables for the mocked interface functions.
 */
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

/**
 * Convert a string of '1's and '0's to a `PunchReading` struct.
 *
 * @param str A string of length 12 consisting of '1's and '0's.
 * @return PunchReading struct representing the punched holes.
 */
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


/**
 * Print an array of saved sensor values.
 *
 * @param vals An array of 13 uint16_t sensor values.
 */
void printSavedSensorVals(uint16_t *vals) {
  Serial.print("[");
  for (int i = 0; i < 12; i++) {
    Serial.print(vals[i]);
    Serial.print(", ");
  }
  Serial.print(vals[12]);
  Serial.print("]");
}

/**
 * Mocked function for turning on even LEDs.
 */
void evenLEDsOn() {
  evenLEDsOnCalled = true;
}

/**
 * Mocked function for turning off even LEDs.
 */
void evenLEDsOff() {
  evenLEDsOffCalled = true;
}

/**
 * Mocked function for turning on odd LEDs.
 */
void oddLEDsOn() {
  oddLEDsOnCalled = true;
}

/**
 * Mocked function for turning off odd LEDs.
 */
void oddLEDsOff() {
  oddLEDsOffCalled = true;
}

/**
 * Mocked function for sending a sensor reading to the photodiode state machine.
 */
void sendSensorReading(SensorReading reading) {
  pdState = updatePhotodiodeState(pdState, reading);
}

/**
 * Mocked function for sending a punch reading to the card processing state machine.
 */
void sendPunchReading(PunchReading reading) {
  sendPunchReadingCalled = true;
  sentPunchReading = reading;

  #ifndef UNIT_TESTING
  cpState = updateCardProcState(cpState, reading);
  #endif // UNIT_TESTING
}

/**
 * Mocked function for sending a column value to the stream processing state machine.
 */
void sendColumn(uint16_t col) {
  sendColumnCalled = true;
  sentCol = col;

  #ifndef UNIT_TESTING
  sendByte(colToByte(col));
  //spState = updateStreamProcState(spState, col, false);
  #endif // UNIT_TESTING
}

/**
 * Mocked function for signaling the end of a card to the stream processing state machine.
 */
void sendCardEnd() {
  sendCardEndCalled = true;

  #ifndef UNIT_TESTING
  sendByte('\n');
  //spState = updateStreamProcState(spState, 0, true);
  #endif // UNIT_TESTING
}

/**
 * Mocked function for sending a byte to the serial interface.
 */
void sendByte(char c) {
  sendByteCalled = true;
  sentByte = c;
  #ifdef SOFTWARE_INTEGRATION_TESTING
    Serial.write(c);
  #endif
}

#endif // TESTING
