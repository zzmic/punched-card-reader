#ifndef CARD_PROCESSOR_H
#define CARD_PROCESSOR_H

/**
 * Structure representing a punched card reading of 12 holes.
 */
typedef struct {
  bool holes[12];
} PunchReading;

/**
 * Enumeration representing the possible states of the card processor.
 */
typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} CardProcState;

/**
 * Structure representing the full state of the card processor,
 * including the current state and the previous punched reading.
 */
typedef struct {
  CardProcState state;
  PunchReading prevPunched;
} FullCardProcState;

void initCardProcessor();

void sendPunchReading(PunchReading& reading);

#ifdef TESTING
FullCardProcState updateCardProcState(FullCardProcState& currState, PunchReading& punched);
#endif // TESTING

#endif // CARD_PROCESSOR_H
