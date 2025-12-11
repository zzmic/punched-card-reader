//#define UNIT_TESTING
//#define SOFTWARE_INTEGRATION_TESTING
//#define HARDWARE_TESTING

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
volatile char buffer[BUF_LEN];
volatile int start = 0;
volatile int end = 0;

FspTimer myTimer;
volatile bool finished_software_integration_tests;
volatile char curReading[12];

static void timerISR2(timer_callback_args_t *p_args) {
  SensorReading curReading = readSensors();
  sendSensorReading(curReading);
  #ifdef SOFTWARE_INTEGRATION_TESTING
    if (!finished_software_integration_tests && checkMessages()) {
      finished_software_integration_tests = true;
    }
  #endif
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
  bool ok = myTimer.begin(TIMER_MODE_PERIODIC, GPT_TIMER, channel, 4000, 50.0, &timerISR2); // complete 4-state cycle at 1 kHz frequency

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

void loop() {
  if (start != end) {
    Serial.print(buffer[start]);
    start = (start + 1) & 0x7F;
  }

  #ifdef SOFTWARE_INTEGRATION_TESTING
  if (finished_software_integration_tests) {
    Serial.println("finished software integration test (if only '};\n' was printed out, it passed)");
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
