--------------------------- MODULE PunchedCardReader ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANT
    N \* Number of columns on the punched card.

VARIABLES
    pdState,    \* Current state of the photodiode driver (LEDS_ON or LEDS_OFF).
    cpState,    \* Current state of the card processor (IDLE or READING).
    pdDetected, \* Boolean value indicating if the photodiode has detected a hole in the current column.
    dataReady,  \* Boolean value indicating if data is ready for the card processor.
    cardData,   \* Set of (index, bit) pairs representing the data read from the card so far.
    cardPunches \* Set of (index, bit) pairs representing card punches.

(* Instance of the photodiode driver. *)
PDInstance == INSTANCE PhotodiodeDriver
    WITH pdState <- pdState,
         cpState <- cpState,
         pdDetected <- pdDetected,
         dataReady <- dataReady,
         cardData <- cardData,
         N <- N,
         LEDS_ON <- "LEDS_ON",
         LEDS_OFF <- "LEDS_OFF",
         IDLE <- "IDLE",
         READING <- "READING",
         cardPunches <- cardPunches

(* Instance of the card processor. *)
CPInstance == INSTANCE CardProcessor
    WITH cpState <- cpState,
         pdState <- pdState,
         pdDetected <- pdDetected,
         dataReady <- dataReady,
         cardData <- cardData,
         N <- N,
         LEDS_ON <- "LEDS_ON",
         LEDS_OFF <- "LEDS_OFF",
         IDLE <- "IDLE",
         READING <- "READING",
         cardPunches <- cardPunches

(* Initial state of the whole system. *)
Init ==
    /\ PDInstance!Init
    /\ CPInstance!Init
    /\ cardPunches \in [0..(N - 1) -> {0, 1}]

(* Next-state relation for the whole system. *)
Next ==
    \/
        /\ PDInstance!PDNext
        /\ UNCHANGED cardPunches
    \/
        /\ CPInstance!CPNext
        /\ UNCHANGED cardPunches

(* Specification of the whole system. *)
Spec ==
    Init /\ [][Next]_<< pdState, cpState, pdDetected, dataReady, cardData, cardPunches >>
--------------------------------------------------------------------------------
(* Type invariant for the whole system. *)
TypeInvariant ==
    /\ pdState \in {"LEDS_ON", "LEDS_OFF"}
    /\ cpState \in {"IDLE", "READING"}
    /\ pdDetected \in BOOLEAN
    /\ dataReady \in BOOLEAN
    /\ cardPunches \in [0..(N - 1) -> {0, 1}]
    /\ cardData \subseteq (0..(N - 1)) \X {0, 1}
    /\ \A <<i, b>> \in cardData: i \in 0..(N - 1) /\ b \in {0, 1}

(* Safety invariant for the whole system. *)
SafetyInvariant ==
    /\ (cpState = "IDLE" => pdState = "LEDS_OFF" /\ ~dataReady)
    /\ (dataReady => pdState = "LEDS_OFF" /\ cpState = "READING")
    /\ (pdState = "LEDS_ON" => cpState = "READING")
    /\ (cpState = "IDLE" /\ cardData /= {} =>
        cardData = {<< i, cardPunches[i] >>: i \in 0..(N - 1)})

(* Invariant for the whole system. *)
Invariant ==
    TypeInvariant /\ SafetyInvariant
--------------------------------------------------------------------------------
(* Main theorem stating that the specification implies the invariant always holds. *)
THEOREM Spec => []Invariant
================================================================================
