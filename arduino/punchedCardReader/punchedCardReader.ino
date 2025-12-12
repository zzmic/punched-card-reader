// #define UNIT_TESTING
// #define SOFTWARE_INTEGRATION_TESTING
// #define HARDWARE_TESTING

#include <Arduino.h>
#include <FspTimer.h>

#if defined(UNIT_TESTING) || defined(SOFTWARE_INTEGRATION_TESTING)
  #define TESTING
#endif

#include "sensors.h"
#include "photodiodeDriver.h"
#include "cardProcessor.h"
#include "streamProcessor.h"
#include "computer.h"
#include "wdt.h"

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
 * Constants and variables for buffering serial output.
 */
#define BUF_LEN 128
volatile char buffer[BUF_LEN];
volatile int start = 0;
volatile int end = 0;

/**
 * Timer object and testing flags.
 */
FspTimer myTimer;
volatile bool finished_software_integration_tests;
volatile char curReading[12];

/**
 * Timer interrupt service routine (ISR).
 *
 * This function is called at a fixed rate to read sensor data and process it.
 *
 * @param p_args Pointer to timer callback arguments (not used).
 */
static void timerISR(timer_callback_args_t *p_args) {
  SensorReading curReading = readSensors();
  sendSensorReading(curReading);

  #ifdef SOFTWARE_INTEGRATION_TESTING
    if (!finished_software_integration_tests && checkMessages()) {
      finished_software_integration_tests = true;
    }
  #endif
}

/**
 * Setup function.
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

  // Init and pet WDT to kick it off
  #ifndef UNIT_TESTING
  initWDT();
  petWDT();
  #endif // UNIT_TESTING

  // Define timer type and find an available channel
  uint8_t timerType = GPT_TIMER;
  int8_t channel = FspTimer::get_available_timer(timerType);

  if (channel < 0) {
    Serial.println("No free GPT timer available");
    while (1);
  }

  // Configure the timer
  // Parameters: mode, type, channel, frequency (Hz), dutyCycle (for PWM, 50% for periodic), callback function
  bool ok = myTimer.begin(TIMER_MODE_PERIODIC, GPT_TIMER, channel, 4000, 50.0, &timerISR); // complete 4-state cycle at 1 kHz frequency

  if (!ok) {
    Serial.println("Timer initialization failed");
    while (1);
  }

  myTimer.setup_overflow_irq();
  // Open the timer (necessary for the R4)
  myTimer.open();

  // Start the timer
  myTimer.start();
}

/**
 * Main loop function.
 */
void loop() {
  noInterrupts();
  bool hasData = (start != end);
  char b = 0;
  if (hasData) {
    b = buffer[start];
    start = (start + 1) & 0x7F;
  }
  interrupts();

  if (hasData) {
    Serial.print(b);
  }

  #ifdef SOFTWARE_INTEGRATION_TESTING
  if (finished_software_integration_tests) {
    Serial.println("finished software integration test (if only '};<newline>' was printed out, it passed)");
    while(1);
  }
  #endif

  #ifdef HARDWARE_TESTING
  for (int i = 0; i < 12; i++) {
    Serial.print(curReading[i]);
  }
  Serial.println("");
  #endif
}
