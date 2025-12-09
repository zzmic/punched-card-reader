#ifndef CARD_PROCESSOR_H
#define CARD_PROCESSOR_H

#include "stdint.h"

#define HOLES_COUNT 12

/**
 * Enumeration representing the possible states of the card processor.
 */
typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} CardProcessorState;

/**
 * Structure representing a punched card reading of 12 holes.
 * holes[0] would represent the [12] hole on the card
 * holes[1-11] would represent the [11]->[0-9]
 */
typedef struct {
  bool holes[HOLES_COUNT];
} PunchReadings;

/**
 * Structure representing the full state of the card processor,
 * including the current state and the previous punched reading.
 */
typedef struct {
  CardProcessorState state;
  PunchReadings prevPunched;
} CardProcessorData;

CardProcessorData updateCardProcessorData(CardProcessorData current, PunchReadings punched);

void initCardProcessor();
void sendPunchReadings(PunchReadings punched);

#endif // CARD_PROCESSOR_H
