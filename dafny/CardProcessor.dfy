include "Utilities.dfy"

module CardProcessorModule {
  import Utils = UtilitiesModule

  datatype CardState = WAIT_FOR_CARD | WAIT_FOR_COLUMN | COLUMN_ENDED

  datatype ProcessEventResult = ProcessEventResult(
    column: Utils.arrayOfLength12<bool>,
    card_ended: bool,
    output_ready: bool
  )

  class CardProcessor {
    var state: CardState
    var prev_punched: Utils.arrayOfLength13<bool>

    constructor ()
      ensures state == WAIT_FOR_CARD
      ensures fresh(prev_punched) && prev_punched.Length == 13
      ensures Utils.IsAllFalse(prev_punched)
    {
      state := WAIT_FOR_CARD;
      prev_punched := new bool[13](_ => false);
    }

    method ProcessEvent(punched: Utils.arrayOfLength13<bool>) returns (res: ProcessEventResult)
      modifies this, prev_punched
      ensures (&& old(state == WAIT_FOR_CARD)
               && old(Utils.IsAllFalse(punched))) ==>
                (&& state == WAIT_FOR_COLUMN
                 && Utils.IsAllFalse(prev_punched))
      ensures (&& old(state == WAIT_FOR_CARD)
               && !old(Utils.IsAllFalse(punched))) ==>
                (&& state == WAIT_FOR_CARD
                 /* Reference: https://www.cs.umd.edu/class/fall2025/cmsc433/Arrays.html#(part._.Array_vs_.Sequence).
                  * `old(prev_punched) == prev_punched` may be too strong since it determines whether `prev_punched` is the same object as before.
                  * Thus, we should relax it to only check for value equality.
                  */
                 && old(prev_punched)[..] == prev_punched[..])
      ensures (&& old(state == WAIT_FOR_COLUMN)
               && old(Utils.IsAllTrue(punched))) ==>
                (&& state == WAIT_FOR_CARD
                 && old(prev_punched)[..] == prev_punched[..]
                 && prev_punched[..] == punched[..]
                 && res.card_ended
                 && res.output_ready)
      ensures (&& old(state == WAIT_FOR_COLUMN)
               && old(Utils.IsFallingEdge(prev_punched, punched))) ==>
                (&& state == COLUMN_ENDED
                 && old(prev_punched)[..] == prev_punched[..]
                 && (forall i :: 0 <= i < 12 ==> res.column[i] == prev_punched[i + 1])
                 && res.output_ready)
      ensures (&& old(state == WAIT_FOR_COLUMN)
               && !old(Utils.IsAllTrue(punched))
               && !old(Utils.IsFallingEdge(prev_punched, punched))) ==>
                (&& state == WAIT_FOR_COLUMN
                 && prev_punched[..] == punched[..]
                 && !res.card_ended
                 && !res.output_ready)
      ensures (&& old(state == COLUMN_ENDED)
               && old(Utils.IsAllFalse(punched))) ==>
                (&& state == WAIT_FOR_COLUMN
                 && Utils.IsAllFalse(prev_punched))
      ensures (&& old(state == COLUMN_ENDED)
               && !old(Utils.IsAllFalse(punched))) ==>
                (&& state == COLUMN_ENDED
                 && old(prev_punched)[..] == prev_punched[..])
    {
      var column := new bool[12](_ => false);
      var card_ended := false;
      var output_ready := false;

      match state {
        case WAIT_FOR_CARD =>
          if Utils.IsAllFalse(punched) {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
              invariant forall j :: 0 <= j < i ==> !prev_punched[j]
            {
              prev_punched[i] := false;
              i := i + 1;
            }
            state := WAIT_FOR_COLUMN;
          }
          else {
            // Do nothing and remain in `WAIT_FOR_CARD`.
          }
        case WAIT_FOR_COLUMN =>
          if Utils.IsAllTrue(punched) {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
              invariant forall j :: 0 <= j < i ==> prev_punched[j] == punched[j]
              invariant old(prev_punched) == prev_punched
            {
              prev_punched[i] := punched[i];
              i := i + 1;
            }
            card_ended := true;
            output_ready := true;
            state := WAIT_FOR_CARD;
          }
          else if Utils.IsFallingEdge(prev_punched, punched) {
            var i := 0;
            while i < 12
              invariant 0 <= i <= 12
              invariant forall j :: 0 <= j < i ==> column[j] == prev_punched[j + 1]
              invariant old(prev_punched) == prev_punched
            {
              column[i] := prev_punched[i + 1];
              i := i + 1;
            }
            output_ready := true;
            state := COLUMN_ENDED;
          }
          else {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
              invariant forall j :: 0 <= j < i ==> prev_punched[j] == punched[j]
            {
              prev_punched[i] := punched[i];
              i := i + 1;
            }
          }
        case COLUMN_ENDED =>
          if Utils.IsAllFalse(punched) {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
              invariant forall j :: 0 <= j < i ==> prev_punched[j] == false
            {
              prev_punched[i] := false;
              i := i + 1;
            }
            state := WAIT_FOR_COLUMN;
          }
          else {
            // Do nothing and remain in `COLUMN_ENDED`.
          }
      }

      res := ProcessEventResult(column, card_ended, output_ready);
    }
  }
}
