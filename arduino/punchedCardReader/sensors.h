#ifndef SENSORS_H
#define SENSORS_H

/**
 * Pin configurations.
 *
 * READ_PINS_COUNT: Number of analog pins used for reading sensor values.
 * HALF_EMITTER_PINS_COUNT: Number of emitter pins for even or odd LEDs.
 * EMITTER_PINS_COUNT: Total number of emitter pins.
 */
#define READ_PINS_COUNT 6
#define EMITTER_PINS_COUNT 12
#define HALF_EMITTER_PINS_COUNT EMITTER_PINS_COUNT / 2

/**
 * Structure to hold sensor readings.
 */
typedef struct {
  uint16_t readings[6];
} SensorReading;

void initSensors();

SensorReading readSensors();

void evenLEDsOn();

void evenLEDsOff();

void oddLEDsOn();

void oddLEDsOff();

#endif // SENSORS_H
