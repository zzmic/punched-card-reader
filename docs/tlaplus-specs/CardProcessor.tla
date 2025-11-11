----------------------------- MODULE CardProcessor -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,                 \* Number of columns on the punched card.
    LEDS_ON, LEDS_OFF, \* Photodiode LED states.
    IDLE, READING      \* Card processor states (for reference in guards).

VARIABLES
    pdState,           \* Current state of the photodiode driver (LEDS_ON or LEDS_OFF).
    cpState,           \* Current state of the card processor (IDLE or READING).
    pdDetected,        \* Boolean value indicating if the photodiode has detected a hole in the current column.
    dataReady,         \* Boolean value indicating if data is ready for the card processor.
    cardData,          \* Set of (index, bit) pairs representing the data read from the card so far.
    cardPunches        \* Set of (index, bit) pairs representing card punches.

(* Initial state of the card processor. *)
Init ==
    /\ cpState = IDLE
    /\ pdState = LEDS_OFF
    /\ pdDetected = FALSE
    /\ dataReady = FALSE
    /\ cardData = {}

(* Transition: Insert a card into the reader. *)
InsertCard ==
    /\ cpState = IDLE
    /\ cpState' = READING
    /\ pdState = LEDS_OFF
    /\ cardData' = {}
    /\ pdDetected' = FALSE
    /\ dataReady' = FALSE
    /\ UNCHANGED << pdState >>

(* Transition: Process a column of the card. *)
ProcessColumn ==
    /\ cpState = READING
    /\ dataReady
    /\ LET i == Cardinality(cardData)
            bit == IF pdDetected THEN 1 ELSE 0
        IN
        /\ i < N
        /\ cardData' = cardData \union {<< i, bit >>}
    /\ dataReady' = FALSE
    /\ pdDetected' = FALSE
    /\ UNCHANGED << pdState, cpState, cardPunches >>

(* Transition: Remove a card from the reader. *)
RemoveCard ==
    /\ cpState = READING
    /\ ~dataReady
    /\ Cardinality(cardData) = N
    /\ cpState' = IDLE
    /\ UNCHANGED << pdState, pdDetected, dataReady, cardData, cardPunches >>

(* Next-state relation for the card processor. *)
CPNext ==
    \/ InsertCard
    \/ ProcessColumn
    \/ RemoveCard
================================================================================
