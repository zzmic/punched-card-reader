#include "Arduino.h"
#include "PunchedCardReader.h"

// the setup function runs once when you press reset or power the board
void setup() {
  // initialize digital pin LED_BUILTIN as an output.
  pinMode(LED_BUILTIN, OUTPUT);
  pinMode(READ_READY_EMITTER_PIN, OUTPUT);

  R_PMISC->PWPR_b.B0WI = 0;
  R_PMISC->PWPR_b.PFSWE = 1;

  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PMR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PCR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.PDR = 0;
  R_PFS->PORT[READ_READY_PORT].PIN[READ_READY_PIN].PmnPFS_b.ASEL = 1;

  R_PMISC->PWPR_b.PFSWE = 0;
  R_PMISC->PWPR_b.B0WI = 1;

  for (int i = 0; i < READ_PINS_COUNT; i++) pinMode(ANALOG_PINS[i], INPUT);
  for (int i = 0; i < EMITTER_PINS_COUNT; i++) pinMode(DIGITAL_PINS[i], OUTPUT);
}

// the loop function runs over and over again forever
void loop() {
  digitalWrite(LED_BUILTIN, HIGH);  // turn the LED on (HIGH is the voltage level)
  delay(1000);                      // wait for a second
  digitalWrite(LED_BUILTIN, LOW);   // turn the LED off by making the voltage LOW
  delay(1000);                      // wait for a second
}
