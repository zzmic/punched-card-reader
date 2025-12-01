#ifndef CARD_PROCESSOR_H
#define CARD_PROCESSOR_H

#include "stdint.h"

typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} ProcessorState;

typedef struct {
  bool holes[13];
} PunchReadings;

typedef struct {
  ProcessorState state;
  PunchReadings prevPunched;
} ProcessorData;

ProcessorData updateData(ProcessorData current, PunchReadings punched);

#endif