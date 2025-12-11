#ifndef PHOTODIODE_DRIVER_H
#define PHOTODIODE_DRIVER_H

/**
 * Enumeration for the photodiode driver states.
 */
typedef enum {
  s_ALL_OFF = 0,
  s_EVEN_ON = 1,
  s_ODD_ON = 2,
  s_CALC = 3,
} PhotodiodeDriverState;

/**
 * Structure to hold the full state of the photodiode driver, which includes
 * the current state and the on and off values for each photodiode.
 */
typedef struct {
  PhotodiodeDriverState state;
  uint16_t onVals[12];
  uint16_t offVals[12];
} FullPhotodiodeState;

/**
 * Threshold (minimum difference) to determine if a hole is present.
 * It will be compared against the difference between off and on readings.
 */
#ifdef TESTING
const uint16_t minDiff = 700;
#else
const uint16_t minDiff = 800;
#endif

void initPhotodiodeDriver();

void sendSensorReading(SensorReading& reading);

#ifdef TESTING
FullPhotodiodeState updatePhotodiodeState(FullPhotodiodeState& curState, SensorReading& reading);
#endif // TESTING

#endif // PHOTODIODE_DRIVER_H
