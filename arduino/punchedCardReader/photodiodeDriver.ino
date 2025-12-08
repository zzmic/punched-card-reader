FullPhotodiodeState updatePhotodiodeState(FullPhotodiodeState curState, SensorReading reading) {
  FullPhotodiodeState ret = curState;

  switch(curState.state) {
    case s_ALL_OFF:
    for (int i = 0; i < 6; i++) {
      ret.offVals[2 * i] = reading.readings[i];
      ret.offVals[(2 * i) + 1] = reading.readings[i];
    }
    ret.offVals[12] = reading.readings[6];
    ret.state = s_EVEN_ON;
    evenLEDsOn();
    break;

    case s_EVEN_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[2 * i] = reading.readings[i];
    }
    ret.state = s_ODD_ON;
    evenLEDsOff();
    oddLEDsOn();
    break;

    case s_ODD_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[(2 * i) + 1] = reading.readings[i];
    }
    ret.state = s_CALC;
    oddLEDsOff();
    break;

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

FullPhotodiodeState curPhotodiodeState;

void initPhotodiodeDriver() {
  curPhotodiodeState.state = s_ALL_OFF;
}
