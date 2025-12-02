#ifndef CARD_PROCESSOR_TESTS_H
#define CARD_PROCESSOR_TESTS_H

#include "CardProcessor.h"

typedef struct {
  ProcessorState startState;
  char *prevPunched;
  char *punched;
  ProcessorState endState;
  char *prevPunchedAfter;
  bool emitColumnCalled;
  uint16_t emittedCol;
  bool emitEOFCalled;
} CardProcessorTest;

const int c_NUM_TESTS = 14;

bool emit_column_called;
bool emit_eof_called;
uint16_t emitted_col;

void emitColumn(uint16_t col);
void emitEOF();
void runAllTests();

PunchReadings stringToPunchReading(char *str);

#endif // CARD_PROCESSOR_TESTS_H
