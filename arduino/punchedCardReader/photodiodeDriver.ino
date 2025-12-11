/**
 * Update the photodiode state machine based on the current state and sensor reading.
 *
 * @param curState The current state of the photodiode driver.
 * @param reading The current sensor reading from the photodiodes.
 * @return The updated state of the photodiode driver.
 */
FullPhotodiodeState updatePhotodiodeState(FullPhotodiodeState& curState, SensorReading& reading) {
  FullPhotodiodeState ret = curState;

  switch(curState.state) {
    /* 0-1. */
    case s_ALL_OFF:
    for (int i = 0; i < 6; i++) {
      ret.offVals[2 * i] = reading.readings[i];
      ret.offVals[(2 * i) + 1] = reading.readings[i];
    }
    ret.offVals[12] = reading.readings[6];
    ret.state = s_EVEN_ON;
    evenLEDsOn();
    break;

    /* 1-2. */
    case s_EVEN_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[2 * i] = reading.readings[i];
    }
    ret.state = s_ODD_ON;
    evenLEDsOff();
    oddLEDsOn();
    break;

    /* 2-3. */
    case s_ODD_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[(2 * i) + 1] = reading.readings[i];
    }
    ret.state = s_CALC;
    oddLEDsOff();
    break;

    /* 3-0. */
    case s_CALC:
    PunchReading punched;
    for (int i = 0; i < 12; i++) {
      punched.holes[i] = (curState.onVals[i] - curState.offVals[i]) > minDiff;
    }
    // printPunchReading(punched);
    // Serial.println("\n");
    sendPunchReading(punched);
    ret.state = s_ALL_OFF;
    // TODO: pet watchdog here?
    #ifdef HARDWARE_TESTING
    for (int i = 0; i < 12; i++) {
      if (punched.holes[i]) {
        curReading[i] = '1';
      } else {
        curReading[i] = '0';
      }
    }
    #endif
    break;
  }

  return ret;
}

/**
 * The current state of the photodiode driver.
 * It is declared as volatile since it may be modified in an interrupt context.
 */
volatile FullPhotodiodeState curPhotodiodeState;

/**
 * Initialize the photodiode driver.
 */
void initPhotodiodeDriver() {
  curPhotodiodeState.state = s_ALL_OFF;
  for (int i = 0; i < 12; i++) {
    curPhotodiodeState.offVals[i] = 0;
    curPhotodiodeState.onVals[i] = 0;
  }
}

#ifndef TESTING
/**
 * Send a sensor reading to the photodiode driver, updating its state.
 *
 * @param reading The punched reading to send.
 */
void sendSensorReading(SensorReading& reading) {
  FullPhotodiodeState curState;
  curState.state = curPhotodiodeState.state;
  for (int i = 0; i < 12; i++) {
    curState.onVals[i] = curPhotodiodeState.onVals[i];
    curState.offVals[i] = curPhotodiodeState.offVals[i];
  }

  FullPhotodiodeState nextState = updatePhotodiodeState(curState, reading);

  curPhotodiodeState.state = nextState.state;
  for (int i = 0; i < 12; i++) {
    curPhotodiodeState.onVals[i] = nextState.onVals[i];
    curPhotodiodeState.offVals[i] = nextState.offVals[i];
  }
}
#endif TESTING
