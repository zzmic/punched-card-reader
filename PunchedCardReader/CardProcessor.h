#ifndef CARD_PROCESSOR_H
#define CARD_PROCESSOR_H

#include "stdint.h"

#define HOLES_COUNT 13
#define DATA_BITS_COUNT 12

typedef enum {
  s_WAIT_FOR_CARD = 0,
  s_WAIT_FOR_COLUMN = 1,
  s_COLUMN_ENDED = 2,
} ProcessorState;

typedef struct {
  bool holes[HOLES_COUNT];
} PunchReadings;

typedef struct {
  ProcessorState state;
  PunchReadings prevPunched;
} ProcessorData;

const PunchReadings c_ZEROED_READINGS = { .holes = { false } };

ProcessorData updateProcessorData(ProcessorData current, PunchReadings punched);

#endif