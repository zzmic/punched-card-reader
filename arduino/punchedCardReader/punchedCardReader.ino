#define UNIT_TESTING
// #define SOFTWARE_INTEGRATION_TESTING

#if defined(UNIT_TESTING) || defined(SOFTWARE_INTEGRATION_TESTING)
  #define TESTING
#endif

#include "sensors.h"
#include "photodiodeDriver.h"
#include "cardProcessor.h"
#include "streamProcessor.h"
#include "computer.h"

#ifdef TESTING
  #include "testUtils.h"
#endif // TESTING
#ifdef UNIT_TESTING
  #include "unitTests.h"
#endif // UNIT_TESTING
#ifdef SOFTWARE_INTEGRATION_TESTING
  #include "softwareIntegrationTests.h"
#endif // SOFTWARE_INTEGRATION_TESTING

const unsigned int c_TIMER_INT = 31;
const unsigned int c_PERIOD_MILLISECONDS = 10;
//  period in ms * 1/1000 sec/ms (48 * 1000 * 1000) cycles/sec * (1/1024) scaling factor
const uint32_t c_COUNTER = (c_PERIOD_MILLISECONDS * (48 * 1000 * 1000 / 1024)) / (1000);

void timerISR() {
  // stop the GPT3 counter
  R_GPT3->GTCR_b.CST = 0;

  sensorReading curReading = readSensors();
  sendSensorReading(curReading);

  #ifdef SOFTWARE_INTEGRATION_TESTING
    if (checkMessages()) {
      R_ICU->IELSR_b[c_TIMER_INT].IR = 0;
      NVIC_ClearPendingIRQ((IRQn_Type) c_TIMER_INT);
      Serial.println("\nfinished software integration test");
      return;
    }
  #endif

  // Set up the next noteISR by setting a counter value and turning on GPT3 counter
  R_GPT3->GTPR = c_COUNTER;
  R_ICU->IELSR[c_TIMER_INT] = (0x075 << R_ICU_IELSR_IELS_Pos);
  R_GPT3->GTCR_b.CST = 1;

  // Clear any pending flags
  // MCU side
  R_ICU->IELSR_b[c_TIMER_INT].IR = 0;
  // Clear the pending interrupt on the CPU side
  NVIC_ClearPendingIRQ((IRQn_Type) c_TIMER_INT);
}

void setup() {
  // put your setup code here, to run once:
  Serial.begin(9600);
  while (!Serial);

  initPhotodiodeDriver();
  initCardProcessor();
  initStreamProcessor();

  #ifdef UNIT_TESTING
  runUnitTests();
  #endif // UNIT_TESTING

  // TODO: set up watchdog

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
  R_ICU->IELSR[c_TIMER_INT] = 0;
  // Use the Arm CMSIS API to enable CPU interrupts
  R_ICU->IELSR[c_TIMER_INT] = (0x075 << R_ICU_IELSR_IELS_Pos); // interrupt enabled on GPT3 overflow

  NVIC_SetVector((IRQn_Type) c_TIMER_INT, (uint32_t) &timerISR); // set vector entry to our handler
  NVIC_SetPriority((IRQn_Type) c_TIMER_INT, 13); // Priority lower than Serial (12)
  NVIC_EnableIRQ((IRQn_Type) c_TIMER_INT);

  // kick off first noteISR by setting a counter value and turning on the counter
  R_GPT3->GTPR = 1;
  R_GPT3->GTCR_b.CST = 1;
}

void loop() {

}
