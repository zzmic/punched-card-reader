#define TESTING
#ifndef TESTING
  #include "cardProcessorTests.ino"
#else
  // import actual modules here
#endif

typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} cardProcState;

typedef struct {
  bool holes[13];
} punchReading;

typedef struct {
  cardProcessorState state;
  punchReading prevPunched;
} fullCardProcState;

fullCardProcState updateCardProcState(fullCardProcState currState, punchReading punched) {};
