include "CommonTypes.dfy"

module CardProcessorModule {
  import P = CommonTypesModule

  datatype CardState = WAIT_FOR_CARD | WAIT_FOR_COLUMN | COLUMN_ENDED

  class CardProcessor {
    var state : CardState
    var prev_punched : P.arrayOfLength13<bool>

    constructor ()
      ensures state == WAIT_FOR_CARD
      ensures fresh(prev_punched) && prev_punched.Length == 13
      ensures P.IsAllFalse(prev_punched)
    {
      state := WAIT_FOR_CARD;
      prev_punched := new bool[13](_ => false);
    }

    method ProcessEvent(punched_input : P.arrayOfLength13<bool>)
      returns (
        column_output : P.arrayOfLength12<bool>, card_ended : bool, output_ready : bool
      )
      modifies this, prev_punched
    {
      column_output := new bool[12](_ => false);
      card_ended := false;
      output_ready := false;

      match state {
        case WAIT_FOR_CARD =>
          if P.IsAllFalse(punched_input) {
            state := WAIT_FOR_COLUMN;
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
            {
              prev_punched[i] := false;
              i := i + 1;
            }
          }
          else {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
            {
              prev_punched[i] := punched_input[i];
              i := i + 1;
            }
          }
        case WAIT_FOR_COLUMN =>
          if P.IsAllTrue(punched_input) {
            card_ended := true;
            output_ready := true;
            state := WAIT_FOR_CARD;
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
            {
              prev_punched[i] := punched_input[i];
              i := i + 1;
            }
          }
          else if P.IsFallingEdge(prev_punched, punched_input) {
            output_ready := true;
            state := COLUMN_ENDED;
            var i := 0;
            while i < 12
              invariant 0 <= i <= 12
            {
              column_output[i] := punched_input[i + 1];
              i := i + 1;
            }
          }
          else {
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
            {
              prev_punched[i] := punched_input[i];
              i := i + 1;
            }
          }
        case COLUMN_ENDED =>
          if P.IsAllFalse(punched_input) {
            state := WAIT_FOR_COLUMN;
            var i := 0;
            while i < 13
              modifies prev_punched
              invariant 0 <= i <= 13
            {
              prev_punched[i] := false;
              i := i + 1;
            }
          }
      }
    }
  }
}
