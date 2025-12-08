uint16_t punchedReadingToBinary(PunchReading punched) {
  uint16_t output = 0;
  for (int i = 0; i < 12; i++) {
    output = output << 1;
    if (punched.holes[i]) {
      output += 1;
    }
  }
  return output;
}

FullCardProcState updateCardProcState(FullCardProcState currState, PunchReading punched) {
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

FullCardProcState curCardProcState;

void initCardProcessor() {
  curCardProcState.state = s_WAIT_FOR_CARD;
  for (int i = 0; i < 12; i++) {
    curCardProcState.prevPunched.holes[i] = true;
  }
}

#ifndef TESTING
void sendPunchReading(PunchReading reading) {
  curCardProcState = updateCardProcState(curCardProcState, reading);
}
#endif // TESTING
