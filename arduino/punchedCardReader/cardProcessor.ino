/**
 * Convert a punched card reading to its binary representation.
 *
 * @param punched The punched card reading to convert.
 * @return The binary representation of the punched card reading as a 16-bit unsigned integer.
 */
uint16_t punchedReadingToBinary(PunchReading& punched) {
  uint16_t output = 0;
  for (int i = 0; i < 12; i++) {
    output = output << 1;
    if (punched.holes[i]) {
      output += 1;
    }
  }
  return output;
}

/**
 * Update the state of the card processor based on the current state and the new punched reading.
 *
 * @param currState The current state of the card processor.
 * @param punched The new punched reading to process.
 */
FullCardProcState updateCardProcState(FullCardProcState& currState, PunchReading& punched) {
  PunchReading prevPunched = currState.prevPunched;
  CardProcState state = currState.state;
  FullCardProcState ret = currState;

  bool allHigh = true;
  bool allLow = true;
  bool anyFalling = false;
  for (int i = 0; i < 12; i++) {
    allHigh = allHigh && punched.holes[i];
    allLow = allLow && !punched.holes[i];
    anyFalling = anyFalling || (prevPunched.holes[i] && !punched.holes[i]);
  }

  switch(state) {
    case s_WAIT_FOR_CARD:
    /* 0-1. */
    if (allLow) {
      ret.state = s_WAIT_FOR_COLUMN;
      ret.prevPunched = punched;
    }
    break;

    case s_WAIT_FOR_COLUMN:
    /* 1-0. */
    if (allHigh) {
      ret.state = s_WAIT_FOR_CARD;
      sendCardEnd();
    }
    /* 1-2. */
    else if (anyFalling) {
      ret.state = s_COLUMN_ENDED;
      sendColumn(punchedReadingToBinary(prevPunched));
    }
    /* 1-1a. */
    //  else if (allLow) {
    //   ret.state = s_WAIT_FOR_COLUMN;
    //   ret.prevPunched = punched;
    //   sendColumn(punchedReadingToBinary(prevPunched));
    // }
    /* 1-1b. */
    else {
      ret.prevPunched = punched;
    }
    break;

    case s_COLUMN_ENDED:
    /* 2-1. */
    if (allLow) {
      ret.state = s_WAIT_FOR_COLUMN;
      // Since `allLow` is true, meaning that `punched` is all holes not punched (i.e., all zeros),
      // `ret.prevPunched = punched` is effectively resetting the previous punched reading (to all zeros).
      ret.prevPunched = punched;
    }
    break;
  }

  return ret;
}

volatile FullCardProcState curCardProcState;

/**
 * Initialize the card processor state.
 */
void initCardProcessor() {
  curCardProcState.state = s_WAIT_FOR_CARD;
  for (int i = 0; i < 12; i++) {
    curCardProcState.prevPunched.holes[i] = true;
  }
}

#ifndef TESTING
/**
 * Send a punched reading to the card processor, updating its state.
 *
 * @param reading The punched reading to send.
 */
void sendPunchReading(PunchReading& reading) {
  FullCardProcState curState;
  curState.state = curCardProcState.state;
  for (int i = 0; i < 12; i++) {
    curState.prevPunched.holes[i] = curCardProcState.prevPunched.holes[i];
  }

  FullCardProcState nextState = updateCardProcState(curState, reading);

  curCardProcState.state = nextState.state;
  for (int i = 0; i < 12; i++) {
    curCardProcState.prevPunched.holes[i] = nextState.prevPunched.holes[i];
  }
}
#endif // TESTING
