include "CommonTypes.dfy"

module PhotodiodeDriverModule {
  import P = CommonTypesModule

  datatype DriverState = LEDS_ON | LEDS_OFF

  class PhotodiodeDriver {
    var state : DriverState
    var off_vals : P.arrayOfLength13<int>
    var punched : P.arrayOfLength13<bool>
    const THRESHOLD: int := 4

    constructor ()
      ensures state == LEDS_OFF
      ensures fresh(off_vals) && off_vals.Length == 13
      ensures fresh(punched) && punched.Length == 13
      ensures P.IsAllFalse(punched)
      ensures P.IsAllZero(off_vals)
    {
      state := LEDS_OFF;
      off_vals := new int[13](_ => 0);
      punched  := new bool[13](_ => false);
    }

    method Tick(reading: P.arrayOfLength13<int>)
      modifies this, off_vals, punched
      ensures old(state) == LEDS_OFF ==>
                state == LEDS_ON &&
                (forall i :: 0 <= i < 13 ==> off_vals[i] == reading[i]) &&
                (forall i :: 0 <= i < 13 ==> punched[i] == old(punched[i]))
      ensures old(state) == LEDS_ON ==>
                state == LEDS_OFF &&
                (forall i :: 0 <= i < 13 ==> punched[i] == (reading[i] - old(off_vals[i]) > THRESHOLD)) &&
                (forall i :: 0 <= i < 13 ==> off_vals[i] == old(off_vals[i]))
    {
      match state {
        case LEDS_OFF =>
          var i := 0;
          while i < 13
            modifies off_vals
            invariant 0 <= i <= 13
            invariant forall j :: 0 <= j < i ==> off_vals[j] == reading[j]
          {
            off_vals[i] := reading[i];
            i := i + 1;
          }
          state := LEDS_ON;

        case LEDS_ON =>
          var i := 0;
          while i < 13
            modifies punched
            invariant 0 <= i <= 13
            invariant forall j :: 0 <= j < i ==> punched[j] == (reading[j] - off_vals[j] > THRESHOLD)
          {
            var diff := reading[i] - off_vals[i];
            punched[i] := diff > THRESHOLD;
            i := i + 1;
          }
          state := LEDS_OFF;
      }
    }
  }
}
