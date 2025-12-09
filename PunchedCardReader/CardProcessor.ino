#include "CardProcessor.h"
#include "StreamProcessor.h"

CardProcessorData CurrentCardState;

/**
 * Convert a punched card reading to its binary representation.
 *
 * @param punched The punched card reading to convert.
 * @return The binary representation of the punched card reading as a 16-bit unsigned integer.
 */
uint16_t punchedReadingToBinary(PunchReadings punched) {
  uint16_t output = 0;
  for (int i = 0; i < HOLES_COUNT; i++) {
    if (punched.holes[i]) output += 1 << i;
  }
  return output;
}

/**
 * Update the state of the card processor based on the current state and the new punched reading.
 *
 * @param currState The current state of the card processor.
 * @param punched The new punched reading to process.
 */
CardProcessorData updateCardProcessorData(CardProcessorData current, PunchReadings punched) {
  PunchReadings previous = current.prevPunched;
  CardProcessorState state = current.state;
  CardProcessorData ret = current;

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
    /* 0-1. */
    if (all_low) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = punched;
    }
    break;

    case s_WAIT_FOR_COLUMN:
    /* 1-0. */
    if (all_high) {
      ret.state = s_WAIT_FOR_CARD;
      sendCardEnd();
    /* 1-2. */
    } else if (any_falling) {
      ret.state = s_COLUMN_ENDED;
      sendColumn(punchedReadingToBinary(previous));
    /* 1-1a. */
    } else if (all_low) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = punched;
      sendColumn(punchedReadingToBinary(previous));
    }
    /* 1-1b. */
    else {
      ret.prevPunched = punched;
    }
    break;

    case s_COLUMN_ENDED:
    /* 2-1. */
    if (all_low) {
      ret.state = s_WAIT_FOR_COLUMN;
      // Since `allLow` is true, meaning that `punched` is all holes not punched (i.e., all zeros),
      // `ret.prevPunched = punched` is effectively resetting the previous punched reading (to all zeros).
      ret.prevPunched = punched;
    }
    break;
  }

  return ret;
}

/**
 * Initialize the card processor state.
 */
void initCardProcessor() {
  CurrentCardState.state = s_WAIT_FOR_CARD;
  for (int i = 0; i < HOLES_COUNT; i++) {
    CurrentCardState.prevPunched.holes[i] = true;
  }
}

/**
 * Send a punched reading to the card processor, updating its state.
 *
 * @param reading The punched reading to send.
 */
void sendPunchReading(PunchReadings punched) {
  CurrentCardState = updateCardProcessorData(CurrentCardState, punched);
}