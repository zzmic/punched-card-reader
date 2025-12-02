#include "PhotodiodeDriver.h"

void calibrate() {
  int on_vals_a[6] = { 1023 };
  int off_vals_a[6] = { 1023 };

  int on_vals_b[6] = { 1023 };
  int off_vals_b[6] = { 1023 };

  int on_vals_sense = 1023;
  int off_vals_sense = 1023;

  // First half

  allLEDsOff();
  readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, off_vals_a);

  evenLEDsOn();
  readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, on_vals_a);

  // Second half

  allLEDsOff();
  readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, off_vals_a);

  oddLEDsOn();
  readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, on_vals_b);

  // Sense

  allLEDsOff();
  off_vals_sense = analogRead(c_ARDUINO_SENSE_PIN);

  digitalWrite(c_SENSE_EMITTER_PIN, HIGH);
  on_vals_sense = analogRead(c_ARDUINO_SENSE_PIN);

  // Feed into readings

  for (int i = 0; i < HALF_EMITTER_PINS_COUNT; i++) {
    readings_buffer[i * 2] = on_vals_a[i] - off_vals_a[i];
    readings_buffer[i * 2 + 1] = on_vals_b[i] - off_vals_b[i];
  }
  readings_buffer[EMITTER_PINS_COUNT - 1] = on_vals_sense - off_vals_sense;

  allLEDsOff();
}

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
    // TODO: pet watchdog here?
    break;
  }

  return ret;
}

void initPhotodiodeDriver() {
  CurrentState.state = s_ALL_OFF;
}