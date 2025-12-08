#ifndef CARD_PROCESSOR_H
#define CARD_PROCESSOR_H

typedef struct {
  bool holes[12];
} PunchReading;

typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} CardProcState;

typedef struct {
  CardProcState state;
  PunchReading prevPunched;
} FullCardProcState;

void initCardProcessor();

void sendPunchReading(PunchReading reading);

#ifdef TESTING
FullCardProcState updateCardProcState(FullCardProcState currState, PunchReading punched);
#endif // TESTING

#endif // CARD_PROCESSOR_H
