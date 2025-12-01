#include "Arduino.h"
#include "PunchedCardReader.h"

void hardwareTest() {
    Serial.println("Hardware test begin...");

    writePins(DIGITAL_PINS, DIGITAL_PINS + EMITTER_PINS_COUNT, HIGH);
    delay(250);
    readPins(ANALOG_PINS, ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    delay(250);
    printPins(ANALOG_PINS, ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    writePins(DIGITAL_PINS, DIGITAL_PINS + EMITTER_PINS_COUNT, LOW);
    delay(250);
    readPins(ANALOG_PINS, ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    delay(250);
    printPins(ANALOG_PINS, ANALOG_PINS + READ_PINS_COUNT, readings_buffer);

    Serial.println("Hardware test ok...");
}

void setup() {
  Serial.begin(9600);
  // initialize digital pin LED_BUILTIN as an output.
  pinMode(LED_BUILTIN, OUTPUT);
  pinMode(READ_READY_EMITTER_PIN, OUTPUT);

  for (int i = 0; i < READ_PINS_COUNT; i++) pinMode(ANALOG_PINS[i], INPUT);
  for (int i = 0; i < EMITTER_PINS_COUNT; i++) pinMode(DIGITAL_PINS[i], OUTPUT);

  // Disable write-protect
  R_PMISC->PWPR_b.B0WI = 0;
  R_PMISC->PWPR_b.PFSWE = 1;

  // Configure for analog general-purpose input
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PMR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PCR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PDR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.ASEL = 1;

  // Enable write-protect
  R_PMISC->PWPR_b.PFSWE = 0;
  R_PMISC->PWPR_b.B0WI = 1;

  hardwareTest();
}

void loop() {
  delay(100);
}
