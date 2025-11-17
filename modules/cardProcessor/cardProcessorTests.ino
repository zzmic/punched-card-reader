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
  return output;
}

void printPunchReading(punchReading punched) {
  for (int i = 0; i < 13; i++) {
    if (punched.holes[i]) {
      Serial.print("1");
    } else {
      Serial.print("0");
    }
  }
}

int numTests = 14;
cardProcTest cardProcTests[] = {
  cardProcTest {
    s_WAIT_FOR_CARD,
    "1111111111111",
    "0000000000000",
    s_WAIT_FOR_COLUMN,
    "0000000000000",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_CARD,
    "1111111111111",
    "1010101010101",
    s_WAIT_FOR_CARD,
    "1111111111111",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_CARD,
    "0000000000000",
    "1010101010101",
    s_WAIT_FOR_CARD,
    "0000000000000",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000001010",
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000001110",
    s_WAIT_FOR_COLUMN,
    "1110000001110",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110011001110",
    s_WAIT_FOR_COLUMN,
    "1110011001110",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000000010",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1100000000010",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1000011101011",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000111111",
    "1000011101011",
    s_COLUMN_ENDED,
    "1110000111111",
    true,
    0b110000111111,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1000011100011",
    "1000011101011",
    s_WAIT_FOR_COLUMN,
    "1000011101011",
    false,
    0,
    false,
  },
  cardProcTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1111111111111",
    s_WAIT_FOR_CARD,
    "1110000001010",
    false,
    0,
    true,
  },
  cardProcTest {
    s_COLUMN_ENDED,
    "1011001100110",
    "0001000000000",
    s_COLUMN_ENDED,
    "1011001100110",
    false,
    0,
    false,
  },
  cardProcTest {
    s_COLUMN_ENDED,
    "1011001100110",
    "0000000000000",
    s_WAIT_FOR_COLUMN,
    "0000000000000",
    false,
    0,
    false,
  },
};

bool runTest(cardProcTest test) {
  emitColumnCalled = false;
  emittedCol = 65536;
  emitEOFCalled = false;

  punchReading prevPunched = stringToPunchReading(test.prevPunched);
  punchReading prevPunchedAfter = stringToPunchReading(test.prevPunchedAfter);
  punchReading punched = stringToPunchReading(test.punched);

  fullCardProcState currState = {test.startState, prevPunched};

  fullCardProcState result = updateCardProcState(currState, punched);

  bool correct = true;

  if (test.endState != result.state) {
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    correct = false;
  }

  for (int i = 0; i < 13; i++) {
    if (result.prevPunched.holes[i] != prevPunchedAfter.holes[i]) {
      Serial.print("incorrect prevPunched\n\tExpected: ");
      printPunchReading(prevPunchedAfter);
      Serial.print("\n\tActual: ");
      printPunchReading(result.prevPunched);
      correct = false;
      break;
    }
  }

  if (emitColumnCalled && !test.emitColumnCalled) {
    Serial.println("should not have emitted a column");
    correct = false;
  } else if (!emitColumnCalled && test.emitColumnCalled) {
    Serial.println("should have emitted a column");
    correct = false;
  } else if (test.emitColumnCalled && (emittedCol != test.emittedCol)) {
    Serial.println("emitted incorrect column");
    correct = false;
  }

  if (emitEOFCalled && !test.emitEOFCalled) {
    Serial.println("should not have emitted EOF");
    correct = false;
  } else if (!emitEOFCalled && test.emitEOFCalled) {
    Serial.println("should have emitted EOF");
    correct = false;
  }

  return correct;
}

void runCardProcTests() {
  Serial.println("\n\n ----- STARTING TESTS -----");
  int numWrong = 0;
  for (int i = 0; i < numTests; i++) {
    Serial.print("\nRUNNING TEST ");
    Serial.println(i + 1);
    bool correct = runTest(cardProcTests[i]);
    if (!correct) {
      numWrong += 1;
    } else {
      Serial.println("\tCORRECT :)");
    }
  }

  if (numWrong) {
    Serial.print("\nFailed ");
    Serial.print(numWrong);
    Serial.println(" tests...");
  } else {
    Serial.println("\nAll tests passed :)");
  }
}

