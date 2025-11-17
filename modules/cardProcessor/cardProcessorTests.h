void emitColumn(uint16_t col);
void emitEOF();

punchReading stringToPunchReading(char *str);

typedef struct {
  cardProcState startState;
  char *prevPunched;
  char *punched;
  cardProcState endState;
  char *prevPunchedAfter;
  bool emitColumnCalled;
  uint16_t emittedCol;
  bool emitEOFCalled;
} cardProcTest;

void runAllCardProcTests();
