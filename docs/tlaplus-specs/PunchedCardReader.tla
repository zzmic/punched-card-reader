--------------------------- MODULE PunchedCardReader ---------------------------
EXTENDS Naturals, Sequences

CONSTANT
    CardPunches

ASSUME
    CardPunches \in Seq({0, 1})

VARIABLES
    pdState,
    cpState,
    pdDetected,
    dataReady,
    cardData

(* Instance of the photodiode driver. *)
PDInstance == INSTANCE PhotodiodeDriver
    WITH pdState <- pdState,
         cpState <- cpState,
         pdDetected <- pdDetected,
         dataReady <- dataReady,
         cardData <- cardData,
         LEDS_ON <- "LEDS_ON",
         LEDS_OFF <- "LEDS_OFF",
         IDLE <- "IDLE",
         READING <- "READING",
         CardPunches <- CardPunches

(* Instance of the card processor. *)
CPInstance == INSTANCE CardProcessor
    WITH cpState <- cpState,
         pdState <- pdState,
         pdDetected <- pdDetected,
         dataReady <- dataReady,
         cardData <- cardData,
         LEDS_ON <- "LEDS_ON",
         LEDS_OFF <- "LEDS_OFF",
         IDLE <- "IDLE",
         READING <- "READING",
         CardPunches <- CardPunches

(* Initial state of the whole system. *)
Init ==
    /\ PDInstance!Init
    /\ CPInstance!Init

(* Next-state relation for the whole system. *)
Next ==
    /\ PDInstance!PDNext
    /\ CPInstance!CPNext

(* Specification of the whole system. *)
Spec ==
    Init /\ [][Next]_<< pdState, cpState, pdDetected, dataReady, cardData >>

(* Type invariant for the whole system. *)
TypeInvariant ==
    /\ pdState \in {"LEDS_ON", "LEDS_OFF"}
    /\ cpState \in {"IDLE", "READING"}
    /\ pdDetected \in BOOLEAN
    /\ dataReady \in BOOLEAN
    /\ cardData \in Seq({0, 1})
    /\ Len(cardData) <= Len(CardPunches)

(* Safety invariant for the whole system. *)
SafetyInvariant ==
    /\ (cpState = "IDLE" => pdState = "LEDS_OFF" /\ ~dataReady)
    /\ (dataReady => pdState = "LEDS_OFF" /\ cpState = "READING")
    /\ (pdState = "LEDS_ON" => cpState = "READING")
    /\ (cpState = "IDLE" /\ cardData /= <<>> => cardData = CardPunches)

(* Invariant for the whole system. *)
Invariant ==
    TypeInvariant /\ SafetyInvariant
================================================================================
