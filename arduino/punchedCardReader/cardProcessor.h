typedef struct {
  bool holes[13];
} punchReading;

typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} cardProcState;

typedef struct {
  cardProcState state;
  punchReading prevPunched;
} fullCardProcState;

void initCardProcessor();

void sendPunchReading(punchReading reading);

#ifdef defined(UNIT_TESTING) || defined(SOFTWARE_INTEGRATION_TESTING)
fullCardProcState updateCardProcState(fullCardProcState currState, punchReading punched);
#endif
