uint16_t punchedReadingToBinary(punchReading punched) {
  uint16_t output = 0;
  for (int i = 1; i < 13; i++) {
    output = output << 1;
    if (punched.holes[i]) {
      output += 1;
    }
  }
  return output;
}

fullCardProcState updateCardProcState(fullCardProcState currState, punchReading punched) {
  punchReading prevPunched = currState.prevPunched;
  cardProcState state = currState.state;
  fullCardProcState ret = currState;

  bool allHigh = true;
  bool allLow = true;
  bool anyFalling = false;
  for (int i = 0; i < 13; i++) {
    allHigh = allHigh && punched.holes[i];
    allLow = allLow && !punched.holes[i];
    anyFalling = anyFalling || (prevPunched.holes[i] && !punched.holes[i]);
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
      sendCardEnd();
    } else if (anyFalling) {
      ret.state = s_COLUMN_ENDED;
      sendColumn(punchedReadingToBinary(prevPunched));
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

fullCardProcState curCardProcState;

void initCardProcessor() {
  curCardProcState.state = s_WAIT_FOR_CARD;
  for (int i = 0; i < 13; i++) {
    curCardProcState.prevPunched.holes[i] = true;
  }
}

#ifdef PRODUCTION
void sendPunchReading(punchReading reading) {
  curCardProcState = updateCardProcState(curCardProcState, reading);
}
#endif
