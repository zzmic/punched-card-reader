----------------------------- MODULE CardProcessor -----------------------------
EXTENDS Naturals, Sequences

CONSTANTS
    LEDS_ON, LEDS_OFF, \* Photodiode LED states.
    IDLE, READING,     \* Card processor states (for reference in guards).
    CardPunches        \* Sequence of 0s and 1s representing card punches.

VARIABLES
    pdState,           \* Current state of the photodiode driver (LEDS_ON or LEDS_OFF).
    cpState,           \* Current state of the card processor (IDLE or READING).
    pdDetected,        \* Boolean indicating if the photodiode has detected a hole in the current column.
    dataReady,         \* Boolean indicating if data is ready for the card processor.
    cardData           \* Sequence of bits representing the data read from the card so far.

(* Initial state of the card processor. *)
Init ==
    /\ cpState = IDLE
    /\ pdState = LEDS_OFF
    /\ pdDetected = FALSE
    /\ dataReady = FALSE
    /\ cardData = <<>>

(* Transition: Insert a card into the reader. *)
InsertCard ==
    /\ cpState = IDLE
    /\ cpState' = READING
    /\ pdState = LEDS_OFF
    /\ cardData' = <<>>
    /\ pdDetected' = FALSE
    /\ dataReady' = FALSE
    /\ UNCHANGED << pdState >>

(* Transition: Process a column of the card. *)
ProcessColumn ==
    /\ cpState = READING
    /\ cpState' = READING
    /\ dataReady = TRUE
    /\ dataReady' = FALSE
    /\ cardData' = cardData \o << IF pdDetected THEN 1 ELSE 0 >>
    /\ UNCHANGED << pdState, pdDetected >>

(* Transition: Remove a card from the reader. *)
RemoveCard ==
    /\ cpState = READING
    /\ cpState' = IDLE
    /\ pdState = LEDS_OFF
    /\ ~dataReady
    /\ Len(cardData) = Len(CardPunches)
    /\ UNCHANGED << pdState, pdDetected, dataReady, cardData >>

(* Next-state relation for the card processor. *)
CardProcNext ==
    \/ InsertCard
    \/ ProcessColumn
    \/ RemoveCard
================================================================================
