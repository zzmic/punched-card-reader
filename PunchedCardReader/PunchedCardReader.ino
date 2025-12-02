#include "Arduino.h"
#include "CardProcessor.h"
#include "PunchedCardReader.h"

#define TESTING
#ifdef TESTING
  #include "CardProcessorTests.h"
#else
  // actual modules
#endif

void timerISR() {
  // stop the GPT3 counter
  R_GPT3->GTCR_b.CST = 0;

  sensorReading curReading = readSensors();
  sendSensorReading(curReading);

  #ifdef SOFTWARE_INTEGRATION_TESTING
  bool complete = checkMessages();
  if (complete) {
    // MCU side
    R_ICU->IELSR_b[TIMER_INT].IR = 0;
    // Clear the pending interrupt on the CPU side
    NVIC_ClearPendingIRQ((IRQn_Type) TIMER_INT);
    Serial.println("\nfinished software integration test");
    return;
  }
  #endif

  // Set up the next noteISR by setting a counter value and turning on GPT3 counter
  R_GPT3->GTPR = (5 * (48 * 1000 * 1000 / 1024)) / (1000);
  // ms * 1/1000 sec/ms (48 * 1000 * 1000) cycles/sec * (1/1024) scaling factor
  R_ICU->IELSR[TIMER_INT] = (0x075 << R_ICU_IELSR_IELS_Pos);
  R_GPT3->GTCR_b.CST = 1;
  
  // Remember to clear any pending flags!
  // MCU side
  R_ICU->IELSR_b[TIMER_INT].IR = 0;
  // Clear the pending interrupt on the CPU side
  NVIC_ClearPendingIRQ((IRQn_Type) TIMER_INT);
}

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
    digitalWrite(c_SENSE_EMITTER_PIN, HIGH);
    read_ready_val = analogRead(c_ARDUINO_SENSE_PIN);
    Serial.println(read_ready_val);
    delay(250);
    digitalWrite(c_SENSE_EMITTER_PIN, LOW);
    read_ready_val = analogRead(c_ARDUINO_SENSE_PIN);
    Serial.println(read_ready_val);
    delay(250);

    calibrate();
    printBuffer(readings_buffer, EMITTER_PINS_COUNT);

    Serial.println("Hardware test ok...");
}

void setup() {
  Serial.begin(9600);
  // initialize digital pin LED_BUILTIN as an output.
  pinMode(LED_BUILTIN, OUTPUT);
  pinMode(c_SENSE_EMITTER_PIN, OUTPUT);
  pinMode(c_ARDUINO_SENSE_PIN, INPUT);

  for (int i = 0; i < READ_PINS_COUNT; i++) pinMode(c_ANALOG_PINS[i], INPUT);
  for (int i = 0; i < EMITTER_PINS_COUNT; i++) pinMode(c_DIGITAL_PINS[i], OUTPUT);

  // Disable write-protect
  R_PMISC->PWPR_b.B0WI = 0;
  R_PMISC->PWPR_b.PFSWE = 1;

  // Configure for analog general-purpose input
  R_PFS->PORT[c_SENSE_PORT].PIN[c_SENSE_PIN].PmnPFS_b.PMR = 0;
  R_PFS->PORT[c_SENSE_PORT].PIN[c_SENSE_PIN].PmnPFS_b.PCR = 0;
  R_PFS->PORT[c_SENSE_PORT].PIN[c_SENSE_PIN].PmnPFS_b.PDR = 0;
  R_PFS->PORT[c_SENSE_PORT].PIN[c_SENSE_PIN].PmnPFS_b.ASEL = 1;

  // Enable write-protect
  R_PMISC->PWPR_b.PFSWE = 0;
  R_PMISC->PWPR_b.B0WI = 1;

  // Enable GPT peripheral
  R_MSTP->MSTPCRD_b.MSTPD6 = 0; 
  // Make sure the count isn't started
  R_GPT3->GTCR_b.CST = 0;
  // Make sure nobody else can start the count (see 22.2.5 and 22.2.6)
  R_GPT3->GTSSR = (1 << R_GPT0_GTSSR_CSTRT_Pos); // only started w/ software
  R_GPT3->GTPSR = (1 << R_GPT0_GTPSR_CSTOP_Pos); // only stopped w/ software
  // Divide the GPT3 clock
  R_GPT3->GTCR = R_GPT3->GTCR & ~(0b111 << 24) | (0b101 << 24); 
  // Disable GPT interrupt on ICU for now
  R_ICU->IELSR[TIMER_INT] = 0;
  // Use the Arm CMSIS API to enable CPU interrupts
  R_ICU->IELSR[TIMER_INT] = (0x075 << R_ICU_IELSR_IELS_Pos); // interrupt enabled on GPT3 overflow 

  NVIC_SetVector((IRQn_Type) TIMER_INT, (uint32_t) &timerISR); // set vector entry to our handler
  NVIC_SetPriority((IRQn_Type) TIMER_INT, 13); // Priority lower than Serial (12)
  NVIC_EnableIRQ((IRQn_Type) TIMER_INT);

  // kick off first noteISR by setting a counter value and turning on the counter
  R_GPT3->GTPR = 1;
  R_GPT3->GTCR_b.CST = 1;

  hardwareTest();
}

void loop() {}
