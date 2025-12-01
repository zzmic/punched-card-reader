#include "CardProcessor.h"
#include "CardProcessorTests.h"

uint16_t punchedReadingToBinary(PunchReadings punched) {
  uint16_t output = 0;
  for (int i = 1; i < 13; i++) {
    output = output << 1;
    if (punched.holes[i]) output += 1;
  }
  return output;
}

ProcessorData updateData(ProcessorData current, PunchReadings punched) {
  PunchReadings previous = current.prevPunched;
  ProcessorState state = current.state;
  ProcessorData ret = current;

  bool allHigh = true;
  bool allLow = true;
  bool anyFalling = false;

  for (int i = 0; i < 13; i++) {
    allHigh = allHigh && punched.holes[i];
    allLow = allLow && !punched.holes[i];
    anyFalling = anyFalling || (previous.holes[i] && !punched.holes[i]);
  }

  switch(state) {
    case s_WAIT_FOR_CARD:
    if (allLow) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = punched;
    }
    break;

    case s_WAIT_FOR_COLUMN:
    if (allHigh) {
      ret.state = s_WAIT_FOR_CARD;
      emitEOF();
    } else if (anyFalling) {
      ret.state = s_COLUMN_ENDED;
      emitColumn(punchedReadingToBinary(previous));
    } else {
      ret.prevPunched = punched;
    }
    break;

    case s_COLUMN_ENDED:
    if (allLow) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = punched;
    }
    break;
  }

  return ret;
}