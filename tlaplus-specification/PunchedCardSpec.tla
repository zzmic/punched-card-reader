---------------------------- MODULE PunchedCardSpec ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* Constants representing the data values and special no-data value. *)
CONSTANTS
    DataValues, \* Finite set of possible data values.
    NoData \* Special value representing no data

(* Assumptions about the constants. *)
ASSUME
    /\ NoData \notin DataValues    \* `NoData` is not a valid data value.
    /\ Cardinality(DataValues) > 0 \* There is at least one valid data value.

(* The set of possible states for the punched card reader. *)
States == {"Idle_Read", "Reading"}

VARIABLES
    state,       \* Current state of the reader.
    cardPresent, \* Whether a card is present in the reader.
    cardData,    \* Data currently on the card.
    hostData     \* Data last transmitted to the host.
--------------------------------------------------------------------------------
(* Initial state of the system. *)
Init ==
    /\ state = "Idle_Read"
    /\ cardPresent = FALSE
    /\ cardData = NoData
    /\ hostData = NoData

(* The type-correctness "invariant" (note that it's only a predicate per se). *)
TypeInvariant ==
    /\ state \in States
    /\ cardPresent \in BOOLEAN
    /\ cardData \in DataValues \union {NoData}
    /\ hostData \in DataValues \union {NoData}

(* Insert a card with given data into the reader while in the idle state. *)
(* `Env` prefix indicates this is an environment action. *)
EnvInsertCard(data) ==
    /\ data \in DataValues
    /\ state = "Idle_Read"
    /\ cardPresent = FALSE
    /\ cardPresent' = TRUE
    /\ cardData' = data
    /\ UNCHANGED << state, hostData >>

EnvAction ==
    \E data \in DataValues: EnvInsertCard(data)

(* Start reading the card if present while in the idle state. *)
(* `Dev` prefix indicates this is a device action. *)
DevReadCardStart ==
    /\ cardPresent = TRUE
    /\ state = "Idle_Read"
    /\ state' = "Reading"
    /\ UNCHANGED << cardPresent, cardData, hostData >>

(* Complete reading the card and transmit data to the host. *)
DevReadCardComplete ==
    /\ state = "Reading"
    /\ hostData' = cardData
    /\ cardData' = NoData
    /\ cardPresent = TRUE
    /\ cardPresent' = FALSE
    /\ state' = "Idle_Read"

DevAction == DevReadCardStart \/ DevReadCardComplete

(* The next-state relation combines environment and device actions. *)
Next == EnvAction \/ DevAction

(* Specification of the system. *)
Spec == Init /\ [][Next]_<< state, cardPresent, cardData, hostData >>
--------------------------------------------------------------------------------
(* Invariant ensuring no data is present when no card is in the reader. *)
NoGhostData == (cardPresent = FALSE) => (cardData = NoData)

(* Invariant ensuring reading only occurs when a card is present. *)
ReadIfCardPresent == (state = "Reading") => (cardPresent = TRUE)
--------------------------------------------------------------------------------
(* Theorem(s) to be checked by TLC. *)
THEOREM Spec => []TypeInvariant /\ []NoGhostData /\ []ReadIfCardPresent
================================================================================
