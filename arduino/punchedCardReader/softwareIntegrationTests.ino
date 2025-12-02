#ifdef SOFTWARE_INTEGRATION_TESTING

// simulates reading a card that represents this single line of a program: "};"
integrationTestTimeStep softwareIntTestSteps[] {
  integrationTestTimeStep {
    1,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    2,
    {900,900,900,900,900,900,900},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    3,
    {900,900,900,900,900,900,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    4,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("1111111111111"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    5,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    6,
    {900,900,900,900,900,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    7,
    {900,900,900,900,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    8,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("1111111110000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    9,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    10,
    {500,500,500,500,500,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    11,
    {500,500,500,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    12,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    13,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    14,
    {500,500,500,500,500,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    15,
    {500,900,900,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    16,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0001010000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    17,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    18,
    {500,500,500,900,900,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    19,
    {500,900,900,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    20,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0001011010000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    21,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    22,
    {500,500,500,500,500,500,900},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    23,
    {500,900,900,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    24,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0001010000001"),

    true,
    0b001011010000,
    false,

    true,
    '}',
  },
  integrationTestTimeStep {
    25,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    26,
    {500,500,500,500,500,500,900},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    27,
    {500,500,500,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    28,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000000001"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    29,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    30,
    {500,500,500,500,500,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    31,
    {500,500,500,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    32,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    33,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    34,
    {500,500,500,500,900,900,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    35,
    {500,500,500,500,900,900,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    36,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000011110"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    37,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    38,
    {500,500,500,900,900,900,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    39,
    {500,900,500,500,900,900,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    40,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0001001011110"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    41,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    42,
    {500,500,500,500,500,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    43,
    {500,500,500,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    44,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000000000"),

    true,
    0b001001011110,
    false,

    true,
    ';',
  },
  integrationTestTimeStep {
    45,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    46,
    {500,500,500,500,500,500,500},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    47,
    {500,500,500,500,500,500,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    48,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    49,
    {0,0,0,0,0,0,0},

    true,
    false,
    false,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    50,
    {900,900,900,900,900,900,900},

    false,
    true,
    true,
    false,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    51,
    {900,900,900,900,900,900,0},

    false,
    false,
    false,
    true,

    false,
    stringToPunchReading("0000000000000"),

    false,
    0,
    false,

    false,
    '\0',
  },
  integrationTestTimeStep {
    52,
    {0,0,0,0,0,0,0},

    false,
    false,
    false,
    false,

    true,
    stringToPunchReading("1111111111111"),

    false,
    0,
    true,

    true,
    '\n',
  },
};

int curTimeStep = 0;

sensorReading readSensors() {
  sensorReading output;
  memcpy(&(output.readings), &(softwareIntTestSteps[curTimeStep].reading), 2 * 7);
  return output;
}

bool checkMessages() {
  integrationTestTimeStep expected = softwareIntTestSteps[curTimeStep];

  if (evenLEDsOnCalled != expected.evenLEDsOnCalled) {
    Serial.print("\nIncorrect evenLEDsOn call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.evenLEDsOnCalled);
    Serial.print("\tActual: ");
    Serial.println(evenLEDsOnCalled);
  }

  if (evenLEDsOffCalled != expected.evenLEDsOffCalled) {
    Serial.print("\nIncorrect evenLEDsOff call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.evenLEDsOffCalled);
    Serial.print("\tActual: ");
    Serial.println(evenLEDsOffCalled);
  }

  if (oddLEDsOnCalled != expected.oddLEDsOnCalled) {
    Serial.print("\nIncorrect oddLEDsOn call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.oddLEDsOnCalled);
    Serial.print("\tActual: ");
    Serial.println(oddLEDsOnCalled);
  }

  if (oddLEDsOffCalled != expected.oddLEDsOffCalled) {
    Serial.print("\nIncorrect oddLEDsOff call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.oddLEDsOffCalled);
    Serial.print("\tActual: ");
    Serial.println(oddLEDsOffCalled);
  }

  if (sendPunchReadingCalled != expected.sendPunchReadingCalled) {
    Serial.print("\nIncorrect sendPunchReading call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.sendPunchReadingCalled);
    Serial.print("\tActual: ");
    Serial.println(sendPunchReadingCalled);
  } else if (expected.sendPunchReadingCalled && memcmp(&(sentPunchReading.holes), &(expected.sentPunchReading.holes), 13)) {
    Serial.print("\nIncorrect punchReading sent at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    printPunchReading(expected.sentPunchReading);
    Serial.print("\n\tActual: ");
    printPunchReading(sentPunchReading);
  }

  if (sendColumnCalled != expected.sendColumnCalled) {
    Serial.print("\nIncorrect sendColumn call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.sendColumnCalled);
    Serial.print("\tActual: ");
    Serial.println(sendColumnCalled);
  } else if (expected.sendColumnCalled && sentCol != expected.sentCol) {
    Serial.print("\nIncorrect column sent at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.print(expected.sentCol, BIN);
    Serial.print("\n\tActual: ");
    Serial.print(sentCol, BIN);
  }

  if (sendCardEndCalled != expected.sendCardEndCalled) {
    Serial.print("\nIncorrect sendCardEnd call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.sendCardEndCalled);
    Serial.print("\tActual: ");
    Serial.println(sendCardEndCalled);
  } 

  if (sendByteCalled != expected.sendByteCalled) {
    Serial.print("\nIncorrect sendByte call at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.println(expected.sendByteCalled);
    Serial.print("\tActual: ");
    Serial.println(sendByteCalled);
  } else if (expected.sendByteCalled && sentByte != expected.sentByte) {
    Serial.print("\nIncorrect byte sent at time step ");
    Serial.println(expected.stepNum);

    Serial.print("\tExpected: ");
    Serial.print(expected.sentByte, HEX);
    Serial.print("\n\tActual: ");
    Serial.print(sentByte, HEX);
  }

  resetMockedInterfaceTracking();

  return (++curTimeStep == 52);
}

#endif
