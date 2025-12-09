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
#define SOFTWARE_INTEGRATION_TESTING

#include <Arduino.h>
#include <FspTimer.h>
#include <math.h> // for round()

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

#define BUF_LEN 128
char buffer[BUF_LEN];
int start = 0;
int end = 0;

/**
 * Constants for setting up the GPT3 timer interrupt.
 *
 * c_TIMER_INT: The interrupt number for GPT3.
 * c_PERIOD_MILLISECONDS: The period of the timer interrupt in milliseconds.
 * c_COUNTER: The counter value calculated based on the desired period and clock settings.
 */
const unsigned int c_TIMER_INT = 31;
const unsigned int c_PERIOD_MILLISECONDS = 1;
//  period in ms * 1/1000 sec/ms (48 * 1000 * 1000) cycles/sec * (1/1024) scaling factor
const uint32_t c_COUNTER = (c_PERIOD_MILLISECONDS * (48 * 1000 * 1000 / 1024)) / (1000);

// /**
//  * Timer interrupt handler for processing sensor readings.
//  */
// void TimerHandler() {
//   Serial.println("inside TimerHandler");
// }

FspTimer myTimer;
//volatile int cycle;
volatile bool go;

static void timerISR2(timer_callback_args_t *p_args) {
  if (!go) {
    go = true;
  }
}

/**
 * Timer interrupt service routine (ISR) for handling GPT3 interrupts.
 */
void timerISR() {
  unsigned long start = millis();
  // stop the GPT3 counter
  R_GPT3->GTCR_b.CST = 0;

  SensorReading curReading = readSensors();
  //Serial.println(curReading.readings[0]);
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
  unsigned long end = millis();
  Serial.println(end - start);
}

/**
 * Initialize the system and peripherals.
 */
void setup() {
  // put your setup code here, to run once:
  Serial.begin(115200);
  while (!Serial);

  initSensors();
  initPhotodiodeDriver();
  initCardProcessor();
  initStreamProcessor();

  #ifdef UNIT_TESTING
  runUnitTests();
  #endif // UNIT_TESTING

  // TODO: set up watchdog

  // Define timer type and find an available channel
  uint8_t timerType = GPT_TIMER; 
  int8_t channel = FspTimer::get_available_timer(timerType);

  if (channel < 0) {
    Serial.println("No free GPT timer available");
    while (1);
  }

  // Configure the timer
  // Parameters: mode, type, channel, frequency (Hz), dutyCycle (for PWM, 50% for periodic), callback function
  bool ok = myTimer.begin(TIMER_MODE_PERIODIC, GPT_TIMER, channel, 1000, 50.0, &timerISR2); // 1 Hz frequency

  if (!ok) {
    Serial.println("Timer initialization failed");
    while (1);
  }

  myTimer.setup_overflow_irq();
  // Open the timer (necessary for the R4)
  myTimer.open(); 
  
  // Start the timer
  myTimer.start();
  Serial.println("Timer started!");

  // // Enable GPT peripheral
  // R_MSTP->MSTPCRD_b.MSTPD6 = 0;
  // // Make sure the count isn't started
  // R_GPT3->GTCR_b.CST = 0;
  // // Make sure nobody else can start the count (see 22.2.5 and 22.2.6)
  // R_GPT3->GTSSR = (1 << R_GPT0_GTSSR_CSTRT_Pos); // only started w/ software
  // R_GPT3->GTPSR = (1 << R_GPT0_GTPSR_CSTOP_Pos); // only stopped w/ software
  // // Divide the GPT3 clock
  // R_GPT3->GTCR = R_GPT3->GTCR & ~(0b111 << 24) | (0b101 << 24);
  // // Disable GPT interrupt on ICU for now
  // R_ICU->IELSR[c_TIMER_INT] = 0;
  // // Use the Arm CMSIS API to enable CPU interrupts
  // R_ICU->IELSR[c_TIMER_INT] = (0x075 << R_ICU_IELSR_IELS_Pos); // interrupt enabled on GPT3 overflow

  // NVIC_SetVector((IRQn_Type) c_TIMER_INT, (uint32_t) &timerISR); // set vector entry to our handler
  // NVIC_SetPriority((IRQn_Type) c_TIMER_INT, 13); // Priority lower than Serial (12)
  // NVIC_EnableIRQ((IRQn_Type) c_TIMER_INT);

  // // kick off first noteISR by setting a counter value and turning on the counter
  // R_GPT3->GTPR = 1;
  // R_GPT3->GTCR_b.CST = 1;

  // ITimer2.init();

  // if (ITimer2.attachInterruptInterval(TIMER_INTERVAL_MS, TimerHandler))
  //   Serial.println("Starting  ITimer OK, millis() = " + String(millis()));
  // else
  //   Serial.println("Can't set ITimer. Select another freq. or timer");
}

void loop() {
  if (go) {
    SensorReading curReading = readSensors();
    sendSensorReading(curReading);

    #ifdef SOFTWARE_INTEGRATION_TESTING
      if (checkMessages()) {
        Serial.println("integration testing done");
        while(1);
      }
    #endif
    go = false;
  }  
  
  // if (start != end) {
  //   Serial.print(buffer[start]);
  //   start = (start + 1) & 0x7F;
  // }
}
