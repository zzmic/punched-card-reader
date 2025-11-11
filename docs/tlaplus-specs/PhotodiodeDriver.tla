--------------------------- MODULE PhotodiodeDriver ----------------------------
EXTENDS Naturals, Sequences, TLC

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

(* Initial state of the photodiode driver. *)
Init ==
    /\ pdState = LEDS_OFF
    /\ cpState = IDLE
    /\ pdDetected = FALSE
    /\ dataReady = FALSE
    /\ cardData = <<>>

(* Transition: Photodiode LED turns ON to read the next column (i.e., when the card is being read and ready for the next column). *)
PD_OffToOn ==
    /\ pdState = LEDS_OFF
    /\ pdState' = LEDS_ON
    /\ cpState = READING
    /\ ~dataReady
    /\ Len(cardData) < Len(CardPunches)
    /\ UNCHANGED << cpState, pdDetected, dataReady, cardData >>

(* Transition: Photodiode LED turns OFF after reading the current column and updates detection status. *)
PD_OnToOff ==
    /\ pdState = LEDS_ON
    /\ pdState' = LEDS_OFF
    /\ cpState = READING
    /\ pdDetected' = (CardPunches[Len(cardData)] = 1)
    /\ dataReady' = TRUE
    /\ UNCHANGED << cpState, cardData >>

(* Next-state relation for the photodiode driver. *)
PDNext ==
    \/ PD_OffToOn
    \/ PD_OnToOff
================================================================================
