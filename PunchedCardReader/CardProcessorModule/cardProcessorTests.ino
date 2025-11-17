#include "cardProcessor.h"

bool emitColumnCalled;
uint16_t emittedCol;
void emitColumn(uint16_t col) {
  emitColumnCalled = true;
  emittedCol = col;
}

bool emitEOFCalled;
void emitEOF() {
  emitEOFCalled = true;
}

punchReading stringToPunchReading(char *str) {
  punchReading output;
  for (int i = 0; i < 13; i++) {
    if (str[i] == '1') {
      output.holes[i] = true;
    } else {
      output.holes[i] = false;
    }
  }
  return output
}

typedef struct {
  cardProcState startState;
  char *prevPunched;
  char *punched;
  cardProcState endState;
  char *prevPunchedAfter;
  bool emitColumnCalled;
  uint16_t emittedCol;
  bool emitEOFCalled;
} test;

char *runTest(test t) {
  emitColumnCalled = false;
  emittedCol = 65536;
  emitEOFCalled = false;

  punchReading prevPunched = initializePunchReading(test.prevPunched);
  punchReading prevPunchedAfter = initializePunchReading(test.prevPunchedAfter);
  punchReading punched = initializePunchReading(test.punched);

  fullCardProcState currState = {test.startState, prevPunched};

  fullCardProcState result = updateCardProcState(currState, punched);

  if (test.endState != result.state) {
    return "incorrect end state";
  }

  for (int i = 0; i < 13; i++) {
    if (result.prevPunched.holes[i] != prevPunchedAfter.holes[i]) {
      return "incorrect prevPunched";
    }
  }

  if (emitColumnCalled && !test.emitColumnCalled) {
    return "should not have emitted a column";
  } else if (!emitColumnCalled && test.emitColumnCalled) {
    return "should have emitted a column";
  } else if (test.emitColumnCalled && (emittedCol != test.emittedCol)) {
    return "emitted incorrect column";
  }

  if (emitEOFCalled && !test.emitEOFCalled) {
    return "should not have emitted EOF";
  } else if (!emitEOFCalled && test.emitEOFCalled) {
    return "should have emitted EOF";
  }

  return NULL;
}

