#ifndef PHOTODIODE_DRIVER_H
#define PHOTODIODE_DRIVER_H

#include "Arduino.h"
#include "CardProcessor.h"
#include "stdint.h"

/**
 * Enumeration for the photodiode driver states.
 */
typedef enum {
  s_ALL_OFF = 0,
  s_EVEN_ON = 1,
  s_ODD_ON = 2,
  s_CALC = 3,
} PhotodiodeState;

/**
 * Structure to hold the full state of the photodiode driver, which includes
 * the current state and the on and off values for each photodiode.
 */
typedef struct {
  PhotodiodeState state;
  int onVals[12];
  int offVals[12];
} PhotodiodeData;

typedef struct {
  int readings[7];
} SensorReadings;

/**
 * Threshold (minimum difference) to determine if a hole is present.
 */
const uint16_t c_MIN_DIFF = 700;

PhotodiodeData updatePhotodiodeData(PhotodiodeData current, SensorReadings readings);

void initPhotodiodeDriver();
void sendSensorReading(SensorReadings readings);

#endif // PHOTODIODE_DRIVER_H
