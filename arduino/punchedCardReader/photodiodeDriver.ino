/**
 * Update the photodiode state machine based on the current state and sensor reading.
 * @param curState The current state of the photodiode driver.
 * @param reading The current sensor reading from the photodiodes.
 * @return The updated state of the photodiode driver.
 */
FullPhotodiodeState updatePhotodiodeState(FullPhotodiodeState curState, SensorReading reading) {
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
    sendPunchReading(punched);
    ret.state = s_ALL_OFF;
    // TODO: pet watchdog here?
    break;
  }

  return ret;
}

/**
 * Current state of the photodiode driver.
 */
FullPhotodiodeState curPhotodiodeState;

/**
 * Initialize the photodiode driver.
 */
void initPhotodiodeDriver() {
  curPhotodiodeState.state = s_ALL_OFF;
}

#ifndef TESTING
/**
 * Send a sensor reading to the photodiode driver, updating its state.
 *
 * @param reading The punched reading to send.
 */
void sendSensorReading(SensorReading reading) {
  curPhotodiodeState = updatePhotodiodeState(curPhotodiodeState, reading);
}
#endif TESTING
