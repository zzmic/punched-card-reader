#include "Arduino.h"
#include "CardProcessor.h"
#include "CardProcessorTests.h"

void emitColumn(uint16_t col) {
  emit_column_called = true;
  emitted_col = col;
}

void emitEOF() {
  emit_eof_called = true;
}

PunchReadings stringToPunchReading(char *str) {
  PunchReadings output;
  for (int i = 0; i < 13; i++) {
    if (str[i] == '1') {
      output.holes[i] = true;
    } else {
      output.holes[i] = false;
    }
  }
  return output;
}

void printPunchReading(PunchReadings punched) {
  for (int i = 0; i < 13; i++) {
    if (punched.holes[i]) {
      Serial.print("1");
    } else {
      Serial.print("0");
    }
  }
}

CardProcessorTest allTests[c_NUM_TESTS] = {
  CardProcessorTest {
    s_WAIT_FOR_CARD,
    "1111111111111",
    "0000000000000",
    s_WAIT_FOR_COLUMN,
    "0000000000000",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_CARD,
    "1111111111111",
    "1010101010101",
    s_WAIT_FOR_CARD,
    "1111111111111",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_CARD,
    "0000000000000",
    "1010101010101",
    s_WAIT_FOR_CARD,
    "0000000000000",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000001010",
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000001110",
    s_WAIT_FOR_COLUMN,
    "1110000001110",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110011001110",
    s_WAIT_FOR_COLUMN,
    "1110011001110",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1110000000010",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1100000000010",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1000011101011",
    s_COLUMN_ENDED,
    "1110000001010",
    true,
    0b110000001010,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000111111",
    "1000011101011",
    s_COLUMN_ENDED,
    "1110000111111",
    true,
    0b110000111111,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1000011100011",
    "1000011101011",
    s_WAIT_FOR_COLUMN,
    "1000011101011",
    false,
    0,
    false,
  },
  CardProcessorTest {
    s_WAIT_FOR_COLUMN,
    "1110000001010",
    "1111111111111",
    s_WAIT_FOR_CARD,
    "1110000001010",
    false,
    0,
    true,
  },
  CardProcessorTest {
    s_COLUMN_ENDED,
    "1011001100110",
    "0001000000000",
    s_COLUMN_ENDED,
    "1011001100110",
    false,
    0,
    false,
  },
  CardProcessorTest {
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

bool runTest(CardProcessorTest test) {
  emit_column_called = false;
  emitted_col = 65536;
  emit_eof_called = false;

  PunchReadings previous = stringToPunchReading(test.prevPunched);
  PunchReadings after = stringToPunchReading(test.prevPunchedAfter);
  PunchReadings punched = stringToPunchReading(test.punched);

  ProcessorData current = {test.startState, previous};

  ProcessorData result = updateProcessorData(current, punched);

  bool correct = true;

  if (test.endState != result.state) {
    Serial.print("incorrect end state\n\tExpected: ");
    Serial.println(test.endState);
    Serial.print("\tActual: ");
    Serial.println(result.state);
    correct = false;
  }

  for (int i = 0; i < 13; i++) {
    if (result.prevPunched.holes[i] != previous.holes[i]) {
      Serial.print("incorrect prevPunched\n\tExpected: ");
      printPunchReading(after);
      Serial.print("\n\tActual: ");
      printPunchReading(result.prevPunched);
      correct = false;
      break;
    }
  }

  if (emit_column_called && !test.emitColumnCalled) {
    Serial.println("should not have emitted a column");
    correct = false;
  } else if (!emit_column_called && test.emitColumnCalled) {
    Serial.println("should have emitted a column");
    correct = false;
  } else if (test.emitColumnCalled && (emitted_col != test.emittedCol)) {
    Serial.println("emitted incorrect column");
    correct = false;
  }

  if (emit_eof_called && !test.emitEOFCalled) {
    Serial.println("should not have emitted EOF");
    correct = false;
  } else if (!emit_eof_called && test.emitEOFCalled) {
    Serial.println("should have emitted EOF");
    correct = false;
  }

  return correct;
}

void runAllTests() {
  Serial.println("\n\n ----- STARTING TESTS -----");
  int num_wrong = 0;
  for (int i = 0; i < c_NUM_TESTS; i++) {
    Serial.print("\nRUNNING TEST ");
    Serial.println(i + 1);
    bool correct = runTest(allTests[i]);
    if (!correct) {
      num_wrong += 1;
    } else {
      Serial.println("\tCORRECT :)");
    }
  }

  if (num_wrong) {
    Serial.print("\nFailed ");
    Serial.print(num_wrong);
    Serial.println(" tests...");
  } else {
    Serial.println("\nAll tests passed :)");
  }
}

