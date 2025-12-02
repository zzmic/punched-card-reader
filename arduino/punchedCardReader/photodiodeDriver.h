#ifndef PHOTODIODE_DRIVER_H
#define PHOTODIODE_DRIVER_H

typedef enum {
  s_ALL_OFF = 0,
  s_EVEN_ON = 1,
  s_ODD_ON = 2,
  s_CALC = 3,
} PhotodiodeDriverState;

typedef struct {
  PhotodiodeDriverState state;
  uint16_t onVals[13];
  uint16_t offVals[13];
} FullPhotodiodeState;

const uint16_t minDiff = 700;

void initPhotodiodeDriver();

void sendSensorReading(SensorReading reading);

#ifdef TESTING
FullPhotodiodeState updatePhotodiodeState(FullPhotodiodeState curState, SensorReading reading);
#endif // TESTING

#endif // PHOTODIODE_DRIVER_H
