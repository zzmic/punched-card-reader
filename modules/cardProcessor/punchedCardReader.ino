#include "cardProcessor.h"

#define TESTING
#ifdef TESTING
  #include "cardProcessorTests.h"
#else
  // actual modules
#endif


void setup() {
  // put your setup code here, to run once:
  Serial.begin(9600);
  while (!Serial);

  #ifdef TESTING
    runCardProcTests();
  #endif
}

void loop() {
  
}
