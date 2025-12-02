#ifndef PHOTODIODE_DRIVER_H
#define PHOTODIODE_DRIVER_H

typedef enum {
  s_ALL_OFF = 0,
  s_EVEN_ON = 1,
  s_ODD_ON = 2,
  s_CALC = 3,
} photodiodeDriverState;

typedef struct {
  photodiodeDriverState state;
  uint16_t onVals[13];
  uint16_t offVals[13];
} fullPhotodiodeState;

const uint16_t minDiff = 700;

void initPhotodiodeDriver();

void sendSensorReading(sensorReading reading);

#ifdef TESTING
fullPhotodiodeState updatePhotodiodeState(fullPhotodiodeState curState, sensorReading reading);
#endif // TESTING

#endif // PHOTODIODE_DRIVER_H
