#include "PhotodiodeDriver.h"

PhotodiodeData CurrentState;

PhotodiodeData updatePhotodiodeData(PhotodiodeData current, SensorReadings readings) {
  PhotodiodeData ret = current;

  switch(current.state) {
    case s_ALL_OFF:
    for (int i = 0; i < 6; i++) {
      ret.offVals[2 * i] = readings.readings[i];
      ret.offVals[(2 * i) + 1] = readings.readings[i];
    }
    ret.offVals[12] = readings.readings[6];
    ret.state = s_EVEN_ON;
    evenLEDsOn();
    break;

    case s_EVEN_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[2 * i] = reading.readings[i];
    }
    ret.onVals[12] = reading.readings[6];
    ret.state = s_ODD_ON;
    allLEDsOff();
    oddLEDsOn();
    break;

    case s_ODD_ON:
    for (int i = 0; i < 6; i++) {
      ret.onVals[(2 * i) + 1] = reading.readings[i];
    }
    ret.state = s_CALC;
    allLEDsOff();
    break;

    case s_CALC:
    PunchReadings punched;
    for (int i = 0; i < 13; i++) {
      punched.holes[i] = (curState.onVals[i] - curState.offVals[i]) > c_MIN_DIFF;
    }
    sendPunchReading(punched);
    ret.state = s_ALL_OFF;
    break;
  }

  return ret;
}

void initPhotodiodeDriver() {
  CurrentState.state = s_ALL_OFF;
}

/**
 * Send a sensor reading to the photodiode driver, updating its state.
 *
 * @param punched The punched reading to send.
 */
void sendSensorReading(SensorReading punched) {
  CurrentState = updatePhotodiodeData(CurrentState, punched);
}