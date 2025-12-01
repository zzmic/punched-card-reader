#include "Arduino.h"
#include "CardProcessor.h"
#include "PunchedCardReader.h"

#define TESTING
#ifdef TESTING
  #include "CardProcessorTests.h"
#else
  // actual modules
#endif

void hardwareTest() {
    Serial.println("Hardware test begin...");

    Serial.println("Testing analog pins...");

    writePins(c_DIGITAL_PINS, c_DIGITAL_PINS + EMITTER_PINS_COUNT, HIGH);
    delay(250);
    readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    delay(250);
    printPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    writePins(c_DIGITAL_PINS, c_DIGITAL_PINS + EMITTER_PINS_COUNT, LOW);
    delay(250);
    readPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    delay(250);
    printPins(c_ANALOG_PINS, c_ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    Serial.println("Testing read ready pin...");

    int read_ready_val = 1023;

    delay(250);
    digitalWrite(c_READ_READY_EMITTER_PIN, HIGH);
    read_ready_val = analogRead(c_ARDUINO_READ_READY_PIN);
    Serial.println(read_ready_val);
    delay(250);
    digitalWrite(c_READ_READY_EMITTER_PIN, LOW);
    read_ready_val = analogRead(c_ARDUINO_READ_READY_PIN);
    Serial.println(read_ready_val);
    delay(250);

    Serial.println("Hardware test ok...");
}

void setup() {
  Serial.begin(9600);
  // initialize digital pin LED_BUILTIN as an output.
  pinMode(LED_BUILTIN, OUTPUT);
  pinMode(c_READ_READY_EMITTER_PIN, OUTPUT);
  pinMode(c_ARDUINO_READ_READY_PIN, INPUT);

  for (int i = 0; i < READ_PINS_COUNT; i++) pinMode(c_ANALOG_PINS[i], INPUT);
  for (int i = 0; i < EMITTER_PINS_COUNT; i++) pinMode(c_DIGITAL_PINS[i], OUTPUT);

  // Disable write-protect
  R_PMISC->PWPR_b.B0WI = 0;
  R_PMISC->PWPR_b.PFSWE = 1;

  // Configure for analog general-purpose input
  R_PFS->PORT[c_READ_READY_PORT].PIN[c_READ_READY_PIN].PmnPFS_b.PMR = 0;
  R_PFS->PORT[c_READ_READY_PORT].PIN[c_READ_READY_PIN].PmnPFS_b.PCR = 0;
  R_PFS->PORT[c_READ_READY_PORT].PIN[c_READ_READY_PIN].PmnPFS_b.PDR = 0;
  R_PFS->PORT[c_READ_READY_PORT].PIN[c_READ_READY_PIN].PmnPFS_b.ASEL = 1;

  // Enable write-protect
  R_PMISC->PWPR_b.PFSWE = 0;
  R_PMISC->PWPR_b.B0WI = 1;

  hardwareTest();
}

void loop() {
  delay(100);
}
