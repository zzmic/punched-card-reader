#ifdef UNIT_TESTING

int numPhotodiodeTests = 12;
PhotodiodeTest photodiodeTests[] = {
  PhotodiodeTest {
    1,
    s_ALL_OFF,
    {100,200,150,125,110,105},
    {500,500,500,500,500,500,500,500,500,500,500,500},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    s_EVEN_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    true,
    false,
    false,
    false,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    2,
    s_ALL_OFF,
    {10,30,50,70,60,40},
    {500,500,500,500,500,500,500,500,500,500,500,500},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    s_EVEN_ON,
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    true,
    false,
    false,
    false,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    3,
    s_EVEN_ON,
    {800,950,400,980,905,600},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,0,950,0,400,0,980,0,905,0,600,0},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    4,
    s_EVEN_ON,
    {370,890,460,600,920,890},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {370,0,890,0,460,0,600,0,920,0,890,0},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    5,
    s_EVEN_ON,
    {370,890,460,600,920,890},
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {0,0,0,0,0,0,0,0,0,0,0,0},
    s_ODD_ON,
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {370,0,890,0,460,0,600,0,920,0,890,0},
    false,
    true,
    true,
    false,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    6,
    s_ODD_ON,
    {990,100,980,110,970,120},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,0,950,0,400,0,980,0,905,0,600,0},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,990,950,100,400,980,980,110,905,970,600,120},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    7,
    s_ODD_ON,
    {650,640,520,800,820,1000},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,0,950,0,400,0,980,0,905,0,600,0},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,650,950,640,400,520,980,800,905,820,600,1000},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    8,
    s_ODD_ON,
    {650,640,520,800,820,1000},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {900,0,800,0,700,0,600,0,500,0,400,0},
    s_CALC,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {900,650,800,640,700,520,600,800,500,820,400,1000},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    9,
    s_ODD_ON,
    {650,640,520,800,820,1000},
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {800,0,950,0,400,0,980,0,905,0,600,0},
    s_CALC,
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {800,650,950,640,400,520,980,800,905,820,600,1000},
    false,
    false,
    false,
    true,
    false,
    stringToPunchReading("000000000000"),
  },
  PhotodiodeTest {
    10,
    s_CALC,
    {200,200,200,200,200,200},
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,790,950,100,400,980,980,110,905,970,600,120},
    s_ALL_OFF,
    {100,100,200,200,150,150,125,125,110,110,105,105},
    {800,790,950,100,400,980,980,110,905,970,600,120},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("001001101100"),
  },
  PhotodiodeTest {
    11,
    s_CALC,
    {200,200,200,200,200,200},
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {800,790,950,100,400,980,980,110,905,970,600,120},
    s_ALL_OFF,
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {800,790,950,100,400,980,980,110,905,970,600,120},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("111001101100"),
  },
  PhotodiodeTest {
    12,
    s_CALC,
    {200,200,200,200,200,200},
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {850,450,860,460,870,470,880,480,890,490,900,500},
    s_ALL_OFF,
    {10,10,30,30,50,50,70,70,60,60,40,40},
    {850,450,860,460,870,470,880,480,890,490,900,500},
    false,
    false,
    false,
    false,
    true,
    stringToPunchReading("101010101010"),
  },
};

bool runPhotodiodeTest(PhotodiodeTest test) {
  resetMockedInterfaceTracking();

  FullPhotodiodeState curState;
  curState.state = test.startState;
  memcpy(&(curState.offVals), &(test.offVals), 2 * 12);
  memcpy(&(curState.onVals), &(test.onVals), 2 * 12);

  SensorReading reading;
  memcpy(&(reading.readings), &(test.readings), 2 * 6);

  FullPhotodiodeState result = updatePhotodiodeState(curState, reading);

  if (test.endState != result.state) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    return false;
  }

  for (int i = 0; i < 12; i++) {
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
    for (int i = 0; i < 12; i++) {
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
CardProcTest cardProcTests[] = {
  CardProcTest {
    1,
    s_WAIT_FOR_CARD,
    "111111111111",
    "000000000000",
    s_WAIT_FOR_COLUMN,
    "000000000000",
    false,
    0,
    false,
  },
  CardProcTest {
    2,
    s_WAIT_FOR_CARD,
    "111111111111",
    "010101010101",
    s_WAIT_FOR_CARD,
    "111111111111",
    false,
    0,
    false,
  },
  CardProcTest {
    3,
    s_WAIT_FOR_CARD,
    "000000000000",
    "010101010101",
    s_WAIT_FOR_CARD,
    "000000000000",
    false,
    0,
    false,
  },
  CardProcTest {
    4,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "110000001010",
    s_WAIT_FOR_COLUMN,
    "110000001010",
    false,
    0,
    false,
  },
  CardProcTest {
    5,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "110000001110",
    s_WAIT_FOR_COLUMN,
    "110000001110",
    false,
    0,
    false,
  },
  CardProcTest {
    6,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "110011001110",
    s_WAIT_FOR_COLUMN,
    "110011001110",
    false,
    0,
    false,
  },
  CardProcTest {
    7,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "110000000010",
    s_COLUMN_ENDED,
    "110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcTest {
    8,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "100000000010",
    s_COLUMN_ENDED,
    "110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcTest {
    9,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "000011101011",
    s_COLUMN_ENDED,
    "110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcTest {
    10,
    s_WAIT_FOR_COLUMN,
    "110000111111",
    "000011101011",
    s_COLUMN_ENDED,
    "110000111111",
    true,
    0b110000111111,
    false,
  },
  CardProcTest {
    11,
    s_WAIT_FOR_COLUMN,
    "000011100011",
    "000011101011",
    s_WAIT_FOR_COLUMN,
    "000011101011",
    false,
    0,
    false,
  },
  CardProcTest {
    12,
    s_WAIT_FOR_COLUMN,
    "110000001010",
    "111111111111",
    s_WAIT_FOR_CARD,
    "110000001010",
    false,
    0,
    true,
  },
  CardProcTest {
    13,
    s_COLUMN_ENDED,
    "011001100110",
    "001000000000",
    s_COLUMN_ENDED,
    "011001100110",
    false,
    0,
    false,
  },
  CardProcTest {
    14,
    s_COLUMN_ENDED,
    "011001100110",
    "000000000000",
    s_WAIT_FOR_COLUMN,
    "000000000000",
    false,
    0,
    false,
  },
};

bool runCardProcTest(CardProcTest test) {
  resetMockedInterfaceTracking();

  PunchReading prevPunched = stringToPunchReading(test.prevPunched);
  PunchReading prevPunchedAfter = stringToPunchReading(test.prevPunchedAfter);
  PunchReading punched = stringToPunchReading(test.punched);

  FullCardProcState curState = {test.startState, prevPunched};

  FullCardProcState result = updateCardProcState(curState, punched);

  if (test.endState != result.state) {
    Serial.print("\nFailed test #");
    Serial.println(test.testNum);
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    return false;
  }

  for (int i = 0; i < 12; i++) {
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

// int numStreamProcTests = 14;
// StreamProcTest streamProcTests[] = {
//   StreamProcTest {
//     1,
//     s_TEXT,
//     0x281,
//     false,
//     s_TEXT,
//     true,
//     'a',
//   },
//   StreamProcTest {
//     2,
//     s_TEXT,
//     0x24C,
//     false,
//     s_TEXT,
//     true,
//     '<',
//   },
//   StreamProcTest {
//     3,
//     s_TEXT,
//     0x277,
//     false,
//     s_TEXT,
//     true,
//     unknownChar,
//   },
//   StreamProcTest {
//     4,
//     s_TEXT,
//     0x381,
//     false,
//     s_TEXT,
//     true,
//     unknownChar,
//   },
//   StreamProcTest {
//     5,
//     s_TEXT,
//     0x281,
//     true,
//     s_TEXT,
//     true,
//     '\n',
//   },
//   StreamProcTest {
//     6,
//     s_TEXT,
//     0x181,
//     false,
//     s_BINARY,
//     true,
//     0x81,
//   },
//   StreamProcTest {
//     7,
//     s_TEXT,
//     0x14C,
//     false,
//     s_BINARY,
//     true,
//     0x4C,
//   },
//   StreamProcTest {
//     8,
//     s_BINARY,
//     0x1FF,
//     false,
//     s_BINARY,
//     true,
//     0xFF,
//   },
//   StreamProcTest {
//     9,
//     s_BINARY,
//     0x1D0,
//     false,
//     s_BINARY,
//     true,
//     0xD0,
//   },
//   StreamProcTest {
//     10,
//     s_BINARY,
//     0x1FF,
//     true,
//     s_TEXT,
//     false,
//     '\0', // this value shouldn't matter
//   },
//   StreamProcTest {
//     11,
//     s_BINARY,
//     0x2D0,
//     false,
//     s_TEXT,
//     true,
//     '}',
//   },
//   StreamProcTest {
//     12,
//     s_BINARY,
//     0x2F7,
//     false,
//     s_TEXT,
//     true,
//     '7',
//   },
//   StreamProcTest {
//     13,
//     s_BINARY,
//     0x0F7,
//     false,
//     s_TEXT,
//     true,
//     unknownChar,
//   },
//   StreamProcTest {
//     14,
//     s_BINARY,
//     0x2BD,
//     false,
//     s_TEXT,
//     true,
//     unknownChar,
//   },
// };

// bool runStreamProcTest(StreamProcTest test) {
//   resetMockedInterfaceTracking();

//   StreamProcState result = updateStreamProcState(test.startState, test.col, test.cardEnded);

//   if (test.endState != result) {
//     Serial.print("\nFailed test #");
//     Serial.println(test.testNum);
//     Serial.print("incorrect end state\n\tExpected: ");
//     Serial.println(test.endState);
//     Serial.print("\tActual: ");
//     Serial.println(result);
//     return false;
//   }

//   if (sendByteCalled && !test.sendByteCalled) {
//     Serial.print("\nFailed test #");
//     Serial.println(test.testNum);
//     Serial.println("should not have sent a byte");
//     return false;
//   } else if (!sendByteCalled && test.sendByteCalled) {
//     Serial.print("\nFailed test #");
//     Serial.println(test.testNum);
//     Serial.println("should have sent a byte");
//     return false;
//   } else if (test.sendByteCalled && (sentByte != test.sentByte)) {
//     Serial.print("\nFailed test #");
//     Serial.println(test.testNum);
//     Serial.print("sent incorrect byte\n\tExpected: ");
//     if (test.endState == s_TEXT) {
//       Serial.print(test.sentByte);
//     } else {
//       Serial.print((uint8_t)test.sentByte, HEX);
//     }
//     Serial.print("\n\t\Actual: ");
//     if (test.endState == s_TEXT) {
//       Serial.print(sentByte);
//     } else {
//       Serial.print((uint8_t)sentByte, HEX);
//     }
//     return false;
//   }

//   return true;
// }

// int numHollerithTests = 96;
int numHollerithTests = 7;
EncodingTest hollerithTests[] = {
  EncodingTest {
    0b101100000011,
    '\0',
  },
  EncodingTest {
    0b000000001000,
    '6',
  },
  EncodingTest {
    0b110000000010,
    'q',
  },
  EncodingTest {
    0b001000000110,
    '?',
  },
  EncodingTest {
    0b010000100010,
    '*',
  },
  EncodingTest {
    0b000000000001,
    '9',
  },
  EncodingTest {
    0b101000000001,
    'i',
  },
};

bool runEncodingTest(EncodingTest test) {
  char actual = colToByte(test.code);
  bool success = actual == test.expectedChar;
  if (!success) {
    Serial.print("\tCode: ");
    Serial.print(test.code, BIN);
    Serial.print("\n\tExpected: ");
    Serial.println(test.expectedChar);
    Serial.print("Actual: ");
    Serial.println(actual);
  }
  return success;
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

  // Serial.println("\n\n ----- RUNNING STREAM PROCESSOR UNIT TESTS -----");
  // for (int i = 0; i < numStreamProcTests; i++) {
  //   bool correct = runStreamProcTest(streamProcTests[i]);
  //   if (!correct) {
  //     numWrong += 1;
  //   }
  // }
  // if (numWrong) {
  //   Serial.print("\nFailed ");
  //   Serial.print(numWrong);
  //   Serial.println(" stream processor tests...");
  // } else {
  //   Serial.println("\nAll stream processor unit tests passed :)");
  // }

  Serial.println("\n\n ----- RUNNING HOLLERITH TESTS -----");
  for (int i = 0; i < numHollerithTests; i++) {
    bool correct = runEncodingTest(hollerithTests[i]);
    if (!correct) {
      numWrong += 1;
    }
  }
  if (numWrong) {
    Serial.print("\nFailed ");
    Serial.print(numWrong);
    Serial.println(" hollerith tests...");
  } else {
    Serial.println("\nAll hollerith unit tests passed :)");
  }
}

#endif // UNIT_TESTING
