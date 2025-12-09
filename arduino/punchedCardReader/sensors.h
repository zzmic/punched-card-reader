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
#define EMITTER_PINS_COUNT 4
#define HALF_EMITTER_PINS_COUNT EMITTER_PINS_COUNT / 2

const int c_ANALOG_PINS[6] = { A0, A1, A2, A3, A4, A5 };
const int c_DIGITAL_PINS[4] = { D2, D3, D4, D5 };
// const int c_EVEN_PINS[2] = { D2, D4 };
// const int c_ODD_PINS[2] = { D3, D5 };

// const int c_ANALOG_PINS[6] = { A5, A4, A3, A2, A1, A0 };
// const int c_DIGITAL_PINS[4] = { D5, D4, D3, D2 };
const int c_ODD_PINS[2] = { D2, D4 };
const int c_EVEN_PINS[2] = { D3, D5 };

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
