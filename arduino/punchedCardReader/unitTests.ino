#ifdef UNIT_TESTING

int numPhotodiodeTests = 12;
photodiodeTest photodiodeTests[] = {
  photodiodeTest {
    1,
    s_ALL_OFF,
    {100,200,150,125,110,105,175},
    {500,500,500,500,500,500,500,500,500,500,500,500,500},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    s_EVEN_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    true,
    false,
    false,
    false,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    2,
    s_ALL_OFF,
    {10,30,50,70,60,40,20},
    {500,500,500,500,500,500,500,500,500,500,500,500,500},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    s_EVEN_ON,
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    true,
    false,
    false,
    false,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    3,
    s_EVEN_ON,
    {800,950,400,980,905,600,300},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,0,950,0,400,0,980,0,905,0,600,0,300},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    4,
    s_EVEN_ON,
    {370,890,460,600,920,890,780},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {370,0,890,0,460,0,600,0,920,0,890,0,780},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    5,
    s_EVEN_ON,
    {370,890,460,600,920,890,780},
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {0,0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {370,0,890,0,460,0,600,0,920,0,890,0,780},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    6,
    s_ODD_ON,
    {990,100,980,110,970,120,960},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,0,950,0,400,0,980,0,905,0,600,0,300},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,990,950,100,400,980,980,110,905,970,600,120,300},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    7,
    s_ODD_ON,
    {650,640,520,800,820,1000,900},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,0,950,0,400,0,980,0,905,0,600,0,300},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,650,950,640,400,520,980,800,905,820,600,1000,300},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    8,
    s_ODD_ON,
    {650,640,520,800,820,1000,900},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {900,0,800,0,700,0,600,0,500,0,400,0,300},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {900,650,800,640,700,520,600,800,500,820,400,1000,300},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    9,
    s_ODD_ON,
    {650,640,520,800,820,1000,900},
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {800,0,950,0,400,0,980,0,905,0,600,0,300},
    s_CALC,
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {800,650,950,640,400,520,980,800,905,820,600,1000,300},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("0000000000000"),
  },
  photodiodeTest {
    10,
    s_CALC,
    {200,200,200,200,200,200,200},
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,790,950,100,400,980,980,110,905,970,600,120,300},
    s_ALL_OFF,
    {100,100,200,200,150,150,125,125,110,110,105,105,175},
    {800,790,950,100,400,980,980,110,905,970,600,120,300},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("0010011011000"),
  },
  photodiodeTest {
    11,
    s_CALC,
    {200,200,200,200,200,200,200},
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {800,790,950,100,400,980,980,110,905,970,600,120,300},
    s_ALL_OFF,
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {800,790,950,100,400,980,980,110,905,970,600,120,300},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("1110011011000"),
  },
  photodiodeTest {
    12,
    s_CALC,
    {200,200,200,200,200,200,200},
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {850,450,860,460,870,470,880,480,890,490,900,500,0},
    s_ALL_OFF,
    {10,10,30,30,50,50,70,70,60,60,40,40,20},
    {850,450,860,460,870,470,880,480,890,490,900,500,0},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("1010101010100"),
  },
};

bool runPhotodiodeTest(photodiodeTest test) {
  resetMockedInterfaceTracking();

  fullPhotodiodeState curState;
  curState.state = test.startState;
  memcpy(&(curState.offVals), &(test.offVals), 2 * 13);
  memcpy(&(curState.onVals), &(test.onVals), 2 * 13);

  sensorReading reading;
  memcpy(&(reading.readings), &(test.readings), 2 * 7);

  fullPhotodiodeState result = updatePhotodiodeState(curState, reading);

  if (test.endState != result.state) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    return false;
  }

  for (int i = 0; i < 13; i++) {
    if (result.onVals[i] != test.onValsAfter[i]) {
      Serial.print("\nFailed test #");
      Serial.println(test.testNum);
      Serial.print("incorrect onVals\n\tExpected: ");
      printSavedSensorVals(test.onValsAfter);
      Serial.print("\n\tActual: ");
      printSavedSensorVals(result.onVals);
      return false;
    } else if (result.offVals[i] != test.offValsAfter[i]) {
      Serial.print("\nFailed test #");
      Serial.println(test.testNum);
      Serial.print("incorrect offVals\n\tExpected: ");
      printSavedSensorVals(test.offValsAfter);
      Serial.print("\n\tActual: ");
      printSavedSensorVals(result.offVals);
      return false;
    }
  }

  if (evenLEDsOnCalled != test.evenLEDsOnCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("incorrect value of evenLEDsOnCalled\n\tExpected: ");
    Serial.print(test.evenLEDsOnCalled);
    Serial.print("\n\tActual: ");
    Serial.println(evenLEDsOnCalled);
    return false;
  }

  if (evenLEDsOffCalled != test.evenLEDsOffCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("incorrect value of evenLEDsOffCalled\n\tExpected: ");
    Serial.print(test.evenLEDsOffCalled);
    Serial.print("\n\tActual: ");
    Serial.println(evenLEDsOffCalled);
    return false;
  }

  if (oddLEDsOnCalled != test.oddLEDsOnCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("incorrect value of oddLEDsOnCalled\n\tExpected: ");
    Serial.print(test.oddLEDsOnCalled);
    Serial.print("\n\tActual: ");
    Serial.println(oddLEDsOnCalled);
    return false;
  }

  if (oddLEDsOffCalled != test.oddLEDsOffCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("incorrect value of oddLEDsOffCalled\n\tExpected: ");
    Serial.print(test.oddLEDsOffCalled);
    Serial.print("\n\tActual: ");
    Serial.println(oddLEDsOffCalled);
    return false;
  }

  if (sendPunchReadingCalled != test.sendPunchReadingCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("incorrect value of sendPunchReadingCalled\n\tExpected: ");
    Serial.print(test.sendPunchReadingCalled);
    Serial.print("\n\tActual: ");
    Serial.println(sendPunchReadingCalled);
    return false;
  }

  if (test.sendPunchReadingCalled) {
    for (int i = 0; i < 13; i++) {
      if (sentPunchReading.holes[i] != test.sentPunchReading.holes[i]) {
        Serial.print("\nFailed test #");
        Serial.println(test.testNum);
        Serial.println("incorrect sent punch reading\n\tExpected: ");
        printPunchReading(test.sentPunchReading);
        Serial.print("\n\tActual: ");
        printPunchReading(test.sentPunchReading);
        return false;
      }
    }
  }

  return true;
}

int numCardProcTests = 14;
cardProcTest cardProcTests[] = {
  cardProcTest {
    1,
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
    2,
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
    3,
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
    4,
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
    5,
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
    6,
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
    7,
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
    8,
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
    9,
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
    10,
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
    11,
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
    12,
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
    13,
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
    14,
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

bool runCardProcTest(cardProcTest test) {
  resetMockedInterfaceTracking();  

  punchReading prevPunched = stringToPunchReading(test.prevPunched);
  punchReading prevPunchedAfter = stringToPunchReading(test.prevPunchedAfter);
  punchReading punched = stringToPunchReading(test.punched);

  fullCardProcState curState = {test.startState, prevPunched};

  fullCardProcState result = updateCardProcState(curState, punched);

  if (test.endState != result.state) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    return false;
  }

  for (int i = 0; i < 13; i++) {
    if (result.prevPunched.holes[i] != prevPunchedAfter.holes[i]) {
      Serial.print("\nFailed test #");
      Serial.println(test.testNum);
      Serial.print("incorrect prevPunched\n\tExpected: ");
      printPunchReading(prevPunchedAfter);
      Serial.print("\n\tActual: ");
      printPunchReading(result.prevPunched);
      return false;
    }
  }

  if (sendColumnCalled && !test.sendColumnCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should not have sent a column");
    return false;
  } else if (!sendColumnCalled && test.sendColumnCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should have sent a column");
    return false;
  } else if (test.sendColumnCalled && (sentCol != test.sentCol)) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("sent incorrect column\n\tExpected: ");
    Serial.print(test.sentCol);
    Serial.print("\n\t\Actual: ");
    Serial.println(sentCol);
    return false;
  }

  if (sendCardEndCalled && !test.sendCardEndCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should not have emitted column end");
    return false;
  } else if (!sendCardEndCalled && test.sendCardEndCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should have emitted column end");
    return false;
  }

  return true;
}

int numStreamProcTests = 14;
streamProcTest streamProcTests[] = {
  streamProcTest {
    1,
    s_TEXT,
    0x281,
    false,
    s_TEXT,
    true,
    'a',
  },
  streamProcTest {
    2,
    s_TEXT,
    0x24C,
    false,
    s_TEXT,
    true,
    '<',
  },
  streamProcTest {
    3,
    s_TEXT,
    0x277,
    false,
    s_TEXT,
    true,
    unknownChar,
  },
  streamProcTest {
    4,
    s_TEXT,
    0x381,
    false,
    s_TEXT,
    true,
    unknownChar,
  },
  streamProcTest {
    5,
    s_TEXT,
    0x281,
    true,
    s_TEXT,
    true,
    '\n',
  },
  streamProcTest {
    6,
    s_TEXT,
    0x181,
    false,
    s_BINARY,
    true,
    0x81,
  },
  streamProcTest {
    7,
    s_TEXT,
    0x14C,
    false,
    s_BINARY,
    true,
    0x4C,
  },
  streamProcTest {
    8,
    s_BINARY,
    0x1FF,
    false,
    s_BINARY,
    true,
    0xFF,
  },
  streamProcTest {
    9,
    s_BINARY,
    0x1D0,
    false,
    s_BINARY,
    true,
    0xD0,
  },
  streamProcTest {
    10,
    s_BINARY,
    0x1FF,
    true,
    s_TEXT,
    false,
    '\0', // this value shouldn't matter
  },
  streamProcTest {
    11,
    s_BINARY,
    0x2D0,
    false,
    s_TEXT,
    true,
    '}',
  },
  streamProcTest {
    12,
    s_BINARY,
    0x2F7,
    false,
    s_TEXT,
    true,
    '7',
  },
  streamProcTest {
    13,
    s_BINARY,
    0x0F7,
    false,
    s_TEXT,
    true,
    unknownChar,
  },
  streamProcTest {
    14,
    s_BINARY,
    0x2BD,
    false,
    s_TEXT,
    true,
    unknownChar,
  },
};

bool runStreamProcTest(streamProcTest test) {
  resetMockedInterfaceTracking();

  streamProcState result = updateStreamProcState(test.startState, test.col, test.cardEnded);

  if (test.endState != result) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result);
    return false;
  }

  if (sendByteCalled && !test.sendByteCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should not have sent a byte");
    return false;
  } else if (!sendByteCalled && test.sendByteCalled) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.println("should have sent a byte");
    return false;
  } else if (test.sendByteCalled && (sentByte != test.sentByte)) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("sent incorrect byte\n\tExpected: ");
    if (test.endState == s_TEXT) {
      Serial.print(test.sentByte);
    } else {
      Serial.print((uint8_t)test.sentByte, HEX);
    }
    Serial.print("\n\t\Actual: ");
    if (test.endState == s_TEXT) {
      Serial.print(sentByte);
    } else {
      Serial.print((uint8_t)sentByte, HEX);
    }
    return false;
  }

  return true;
}

void runUnitTests() {
  int numWrong = 0;

  Serial.println("\n\n ----- RUNNING PHOTODIODE DRIVER UNIT TESTS -----");
  for (int i = 0; i < numPhotodiodeTests; i++) {
    bool correct = runPhotodiodeTest(photodiodeTests[i]);
    if (!correct) {
      numWrong += 1;
    }
  }
  if (numWrong) {
    Serial.print("\nFailed ");
    Serial.print(numWrong);
    Serial.println(" photodiode driver tests...");
  } else {
    Serial.println("\nAll photodiode driver unit tests passed :)");
  }

  numWrong = 0;

  Serial.println("\n\n ----- RUNNING CARD PROCESSOR UNIT TESTS -----");
  for (int i = 0; i < numCardProcTests; i++) {
    bool correct = runCardProcTest(cardProcTests[i]);
    if (!correct) {
      numWrong += 1;
    }
  }
  if (numWrong) {
    Serial.print("\nFailed ");
    Serial.print(numWrong);
    Serial.println(" card processor tests...");
  } else {
    Serial.println("\nAll card processor unit tests passed :)");
  }

  numWrong = 0;

  Serial.println("\n\n ----- RUNNING STREAM PROCESSOR UNIT TESTS -----");
  for (int i = 0; i < numStreamProcTests; i++) {
    bool correct = runStreamProcTest(streamProcTests[i]);
    if (!correct) {
      numWrong += 1;
    }
  }
  if (numWrong) {
    Serial.print("\nFailed ");
    Serial.print(numWrong);
    Serial.println(" stream processor tests...");
  } else {
    Serial.println("\nAll stream processor unit tests passed :)");
  }
}

#endif
