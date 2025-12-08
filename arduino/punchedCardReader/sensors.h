#ifndef SENSORS_H
#define SENSORS_H

#define READ_PINS_COUNT 6
#define HALF_EMITTER_PINS_COUNT 6
#define EMITTER_PINS_COUNT 13


// const int c_SENSE_EMITTER_PIN = D12;
// const int c_ANALOG_PINS[6] = {A0, A1, A2, A3, A4, A5};
// const int c_DIGITAL_PINS[13] = {
//     D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, c_SENSE_EMITTER_PIN};
// const int c_EVEN_PINS[6] = {D0, D2, D4, D6, D8, D10};
// const int c_ODD_PINS[6] = {D1, D3, D5, D7, D9, D11};

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
