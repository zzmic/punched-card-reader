include "Utilities.dfy"

/**
  * Module for controlling the photodiode driver.
  */
module PhotodiodeDriverModule {
  import Utils = UtilitiesModule

  /**
    * State type(s) for the photodiode driver.
    */
  datatype DriverState = LEDS_ON | LEDS_OFF

  /**
    * Class for controlling the photodiode driver.
    */
  class PhotodiodeDriver {
    var state: DriverState
    var off_vals: Utils.arrayOfLength13<int>
    var punched: Utils.arrayOfLength13<bool>
    const THRESHOLD: int := 4

    /**
      * Constructor that initializes the photodiode driver.
      */
    constructor ()
      ensures state == LEDS_OFF
      ensures fresh(off_vals) && off_vals.Length == 13
      ensures fresh(punched) && punched.Length == 13
      ensures Utils.IsAllFalse(punched)
      ensures Utils.IsAllZero(off_vals)
    {
      state := LEDS_OFF;
      off_vals := new int[13](_ => 0);
      punched  := new bool[13](_ => false);
    }

    /**
      * Tick the photodiode driver with the current readings.
      *
      * @param reading An array of length 13 representing the current photodiode readings.
      */
    method Tick(reading: Utils.arrayOfLength13<int>)
      modifies this, off_vals, punched
      ensures old(state) == LEDS_OFF ==>
                state == LEDS_ON &&
                (off_vals[..] == reading[..]) &&
                (punched[..] == old(punched)[..])
      ensures old(state) == LEDS_ON ==>
                state == LEDS_OFF &&
                (off_vals[..] == old(off_vals)[..]) &&
                (forall i :: 0 <= i < 13 ==> punched[i] == (reading[i] - old(off_vals[i]) > THRESHOLD))
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
