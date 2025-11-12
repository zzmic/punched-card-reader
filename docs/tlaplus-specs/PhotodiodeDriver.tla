--------------------------- MODULE PhotodiodeDriver ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,                 \* Number of columns on the punched card.
    LEDS_ON, LEDS_OFF, \* Photodiode LED states.
    IDLE, READING      \* Card processor states, where IDLE indicates no card is present,
                       \* and READING indicates a card is inserted and (ready to) being processed.

VARIABLES
    pdState,           \* Current state of the photodiode driver (LEDS_ON or LEDS_OFF).
    cpState,           \* Current state of the card processor (IDLE or READING).
    pdDetected,        \* Boolean value indicating if the photodiode has detected a hole in the current column.
    dataReady,         \* Boolean value indicating if data is ready for the card processor.
    cardData,          \* Set of (index, bit) pairs representing the data read from the card so far.
    cardPunches        \* Set of (index, bit) pairs representing card punches.

(* Initial state of the photodiode driver. *)
Init ==
    /\ pdState = LEDS_OFF
    /\ cpState = IDLE
    /\ pdDetected = FALSE
    /\ dataReady = FALSE
    /\ cardData = {}

(* Transition: Photodiode LED turns ON to read the next column (i.e., when the card is being read and ready for the next column). *)
PD_OffToOn ==
    /\ pdState = LEDS_OFF
    /\ pdState' = LEDS_ON
    /\ cpState = READING
    /\ ~dataReady
    /\ Cardinality(cardData) < Cardinality(DOMAIN cardPunches)
    /\ UNCHANGED << cpState, pdDetected, dataReady, cardData, cardPunches >>

(* Transition: Photodiode LED turns OFF after reading the current column and updates detection status. *)
PD_OnToOff ==
    /\ pdState = LEDS_ON
    /\ cpState = READING
    /\ LET i == Cardinality(cardData)
        IN
            /\ i < N
            /\ pdDetected' = (cardPunches[i] = 1)
            /\ dataReady' = TRUE
    /\ pdState' = LEDS_OFF
    /\ UNCHANGED << cpState, cardData, cardPunches >>

(* Next-state relation for the photodiode driver. *)
PDNext ==
    \/ PD_OffToOn
    \/ PD_OnToOff
================================================================================
