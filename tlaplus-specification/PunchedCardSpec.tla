---------------------------- MODULE PunchedCardSpec ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* Constants representing the data values and special no-data value. *)
CONSTANTS
    DataValues,   \* Finite set of possible data values.
    NoData,       \* Special value representing no data.
    MaxNumOfCards \* Maximum number of cards that can be processed.

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
    hostData,    \* Data last transmitted to the host.
    insertions,  \* Sequence of card insertions.
    deliveries   \* Sequence of data deliveries to the host.
--------------------------------------------------------------------------------
(* Initial state of the system. *)
Init ==
    /\ state = "Idle_Read"
    /\ cardPresent = FALSE
    /\ cardData = NoData
    /\ hostData = NoData
    /\ insertions = <<>>
    /\ deliveries = <<>>

(* The type-correctness "invariant" (note that it's only a predicate per se). *)
TypeInvariant ==
    /\ state \in States
    /\ cardPresent \in BOOLEAN
    /\ cardData \in DataValues \union {NoData}
    /\ hostData \in DataValues \union {NoData}
    /\ insertions \in Seq(DataValues)
    /\ deliveries \in Seq(DataValues)
--------------------------------------------------------------------------------
(* Insert a card with given data into the reader while in the idle state. *)
(* `Env` prefix indicates this is an environment action. *)
EnvInsertCard(data) ==
    /\ data \in DataValues
    /\ state = "Idle_Read"
    /\ cardPresent = FALSE
    /\ cardPresent' = TRUE
    /\ cardData' = data
    /\ insertions' = Append(insertions, data)
    /\ Len(insertions') <= MaxNumOfCards
    /\ UNCHANGED << state, hostData, deliveries >>

EnvAction ==
    \E data \in DataValues: EnvInsertCard(data)

(* Start reading the card if present while in the idle state. *)
(* `Dev` prefix indicates this is a device action. *)
DevReadCardStart ==
    /\ cardPresent = TRUE
    /\ state = "Idle_Read"
    /\ state' = "Reading"
    /\ UNCHANGED << cardPresent, cardData, hostData, insertions, deliveries >>

(* Complete reading the card and transmit data to the host. *)
DevReadCardComplete ==
    /\ state = "Reading"
    /\ state' = "Idle_Read"
    /\ hostData' = cardData
    /\ cardData' = NoData \* It indicates that the card has been read and removed from the device.
    /\ cardPresent = TRUE
    /\ cardPresent' = FALSE
    /\ deliveries' = Append(deliveries, cardData)
    /\ UNCHANGED << insertions >>

DevAction == DevReadCardStart \/ DevReadCardComplete

(* Quiescent step where no action occurs, maintaining all variables. *)
Quiescent ==
    /\ state = "Idle_Read"
    /\ cardPresent = FALSE
    /\ Len(insertions) = Len(deliveries)
    /\ Len(insertions) = MaxNumOfCards
    /\ UNCHANGED << state, cardPresent, cardData, hostData, insertions, deliveries >>

(* The next-state relation combines environment and device actions. *)
Next == EnvAction \/ DevAction \/ Quiescent

(* Specification of the system. *)
Spec == Init /\ [][Next]_<< state, cardPresent, cardData, hostData, insertions, deliveries >>
--------------------------------------------------------------------------------
(* Invariant ensuring that no data is present when no card is in the reader. *)
NoGhostData == (cardPresent = FALSE) => (cardData = NoData)

(* Invariant ensuring that reading only occurs when a card is present. *)
ReadIfCardPresent == (state = "Reading") => (cardPresent = TRUE)

(* Invariant ensuring that the idle state is maintained when no card is present. *)
IdleIfNoCard == (cardPresent = FALSE) => (state = "Idle_Read")

(* Invariant ensuring that `deliveries` is always a prefix of `insertions` with no reordering or duplication. *)
DeliveriesArePrefixOfInsertions == deliveries = SubSeq(insertions, 1, Len(deliveries))

(* Invariant ensuring that the number of insertions and the number of deliveries do not exceed `MaxNumOfCards`. *)
InsertionsAndDeliveriesNotExceedingMaxNumOfCards == Len(insertions) <= MaxNumOfCards /\ Len(deliveries) <= MaxNumOfCards
--------------------------------------------------------------------------------
(* TODO(zzmic): Specify liveness properties. *)

--------------------------------------------------------------------------------
(* The main theorem stating that the specification implies all invariants. *)
THEOREM Spec =>
    /\ []TypeInvariant
    /\ []NoGhostData
    /\ []ReadIfCardPresent
    /\ []IdleIfNoCard
    /\ []DeliveriesArePrefixOfInsertions
    /\ []InsertionsAndDeliveriesNotExceedingMaxNumOfCards
================================================================================
