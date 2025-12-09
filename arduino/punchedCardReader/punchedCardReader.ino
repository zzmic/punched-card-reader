// // Select the timers you're using, here ITimer1
// #define USE_TIMER_2     true
// #define TIMER_INTERVAL_MS        50L

// // To be included only in main(), .ino with setup() to avoid `Multiple Definitions` Linker Error
// #include "TimerInterrupt.h"           //https://github.com/khoih-prog/TimerInterrupt

// // To be included only in main(), .ino with setup() to avoid `Multiple Definitions` Linker Error
// #include "ISR_Timer.h"                //https://github.com/khoih-prog/TimerInterrupt

// #include <TimerInterrupt.hpp>         //https://github.com/khoih-prog/TimerInterrupt
// #include <ISR_Timer.hpp>              //https://github.com/khoih-prog/TimerInterrupt

//#define UNIT_TESTING
//#define SOFTWARE_INTEGRATION_TESTING

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

/**
 * Constants for setting up the GPT3 timer interrupt.
 *
 * c_TIMER_INT: The interrupt number for GPT3.
 * c_PERIOD_MILLISECONDS: The period of the timer interrupt in milliseconds.
 * c_COUNTER: The counter value calculated based on the desired period and clock settings.
 */
const unsigned int c_TIMER_INT = 31;
const unsigned int c_PERIOD_MILLISECONDS = 5;
//  period in ms * 1/1000 sec/ms (48 * 1000 * 1000) cycles/sec * (1/1024) scaling factor
const uint32_t c_COUNTER = (c_PERIOD_MILLISECONDS * (48 * 1000 * 1000 / 1024)) / (1000);

/**
 * Timer interrupt handler for processing sensor readings.
 */
void TimerHandler() {
  Serial.println("inside TimerHandler");
}

/**
 * Timer interrupt service routine (ISR) for handling GPT3 interrupts.
 */
void timerISR() {
  // stop the GPT3 counter
  R_GPT3->GTCR_b.CST = 0;

  SensorReading curReading = readSensors();
  sendSensorReading(curReading);

  #ifdef SOFTWARE_INTEGRATION_TESTING
    if (checkMessages()) {
      R_ICU->IELSR_b[c_TIMER_INT].IR = 0;
      NVIC_ClearPendingIRQ((IRQn_Type) c_TIMER_INT);
      Serial.println("\nfinished software integration test (if nothing else was printed out, it passed)");
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

/**
 * Initialize the system and peripherals.
 */
void setup() {
  // put your setup code here, to run once:
  Serial.begin(9600);
  while (!Serial);

  initSensors();
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

  // ITimer2.init();

  // if (ITimer2.attachInterruptInterval(TIMER_INTERVAL_MS, TimerHandler))
  //   Serial.println("Starting  ITimer OK, millis() = " + String(millis()));
  // else
  //   Serial.println("Can't set ITimer. Select another freq. or timer");
}

void loop() {

}
