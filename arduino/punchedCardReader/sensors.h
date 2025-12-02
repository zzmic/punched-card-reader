typedef struct {
  uint16_t readings[7];
} sensorReading;

void initSensors();

sensorReading readSensors();

void evenLEDsOn();

void evenLEDsOff();

void oddLEDsOn();

void oddLEDsOff();
