#include "CardProcessor.h"
#include "CardProcessorTests.h"

uint16_t punchedReadingToBinary(PunchReadings punched) {
  uint16_t output = 0;
  for (int i = 0; i < DATA_BITS_COUNT; i++) {
    if (punched.holes[i]) output += 1 << i;
  }
  return output;
}

ProcessorData updateProcessorData(ProcessorData current, PunchReadings punched) {
  PunchReadings previous = current.prevPunched;
  ProcessorState state = current.state;
  ProcessorData ret = current;

  bool all_high = true;
  bool all_low = true;
  bool any_falling = false;

  for (int i = 0; i < HOLES_COUNT; i++) {
    all_high = all_high && punched.holes[i];
    all_low = all_low && !punched.holes[i];
    any_falling = any_falling || (previous.holes[i] && !punched.holes[i]);
  }

  switch(state) {
    case s_WAIT_FOR_CARD:
    if (all_low) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = c_ZEROED_READINGS;
    }
    break;

    case s_WAIT_FOR_COLUMN:
    if (all_high) {
      ret.state = s_WAIT_FOR_CARD;
      emitEOF();
    } else if (any_falling) {
      ret.state = s_COLUMN_ENDED;
      emitColumn(punchedReadingToBinary(previous));
    } else {
      ret.prevPunched = punched;
    }
    break;

    case s_COLUMN_ENDED:
    if (all_low) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = c_ZEROED_READINGS;
    }
    break;
  }

  return ret;
}