include "Utilities.dfy"
include "PhotodiodeDriver.dfy"

module PhotodiodeDriverTestsModule {
  import Utils = UtilitiesModule
  import PD = PhotodiodeDriverModule

  method Lemma_PD_Tick_FSM(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    modifies pd, pd.off_vals, pd.punched
    ensures old(pd.state) == PD.LEDS_OFF ==> pd.state == PD.LEDS_ON
    ensures old(pd.state) == PD.LEDS_ON ==> pd.state == PD.LEDS_OFF
  {
    var start_state := pd.state;
    pd.Tick(reading);
  }

  method Lemma_PD_LEDS_Off_Behavior(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    requires pd.state == PD.LEDS_OFF
    modifies pd, pd.off_vals, pd.punched
    ensures pd.state == PD.LEDS_ON
    ensures forall i :: 0 <= i < 13 ==> pd.off_vals[i] == reading[i]
    ensures forall i :: 0 <= i < 13 ==> pd.punched[i] == old(pd.punched[i])
  {
    var old_punched := pd.punched;
    pd.Tick(reading);
  }

  method Lemma_PD_LEDS_On_Behavior(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    requires pd.state == PD.LEDS_ON
    modifies pd, pd.off_vals, pd.punched
    ensures pd.state == PD.LEDS_OFF
    ensures forall i :: 0 <= i < 13 ==> pd.punched[i] == (reading[i] - old(pd.off_vals[i]) > pd.THRESHOLD)
    ensures forall i :: 0 <= i < 13 ==> pd.off_vals[i] == old(pd.off_vals[i])
  {
    var old_off_vals := pd.off_vals;
    pd.Tick(reading);
  }

  method {:test} Test_PD_01()
  {
    var pd := new PD.PhotodiodeDriver();
    assert pd.state == PD.LEDS_OFF;
    // 0000000000000.
    assert Utils.IsAllZero(pd.off_vals);

    // 0000111122223.
    var reading := new int[13];
    reading[0] := 0;
    reading[1] := 0;
    reading[2] := 0;
    reading[3] := 0;
    reading[4] := 1;
    reading[5] := 1;
    reading[6] := 1;
    reading[7] := 1;
    reading[8] := 2;
    reading[9] := 2;
    reading[10] := 2;
    reading[11] := 2;
    reading[12] := 3;
    pd.Tick(reading);

    assert pd.state == PD.LEDS_ON;
    // 0000111122223.
    assert forall i :: 0 <= i < 13 ==> pd.off_vals[i] == reading[i];
  }

  method {:test} Test_PD_02(pd: PD.PhotodiodeDriver)
    modifies pd, pd.off_vals, pd.punched
    requires pd.state == PD.LEDS_OFF
    // 0000000000000.
    requires Utils.IsAllZero(pd.off_vals)
    ensures pd.state == PD.LEDS_ON
    // 0220333344410.
    ensures pd.off_vals[0] == 0
    ensures pd.off_vals[1] == 2
    ensures pd.off_vals[2] == 2
    ensures pd.off_vals[3] == 0
    ensures pd.off_vals[4] == 3
    ensures pd.off_vals[5] == 3
    ensures pd.off_vals[6] == 3
    ensures pd.off_vals[7] == 3
    ensures pd.off_vals[8] == 4
    ensures pd.off_vals[9] == 4
    ensures pd.off_vals[10] == 4
    ensures pd.off_vals[11] == 1
    ensures pd.off_vals[12] == 0
  {
    // 0220333344410.
    var reading := new int[13];
    reading[0] := 0;
    reading[1] := 2;
    reading[2] := 2;
    reading[3] := 0;
    reading[4] := 3;
    reading[5] := 3;
    reading[6] := 3;
    reading[7] := 3;
    reading[8] := 4;
    reading[9] := 4;
    reading[10] := 4;
    reading[11] := 1;
    reading[12] := 0;
    pd.Tick(reading);
  }

  method {:test} Test_PD_03(pd: PD.PhotodiodeDriver)
    modifies pd, pd.off_vals, pd.punched
    requires pd.state == PD.LEDS_ON
    // 0000111122223.
    requires pd.off_vals[0] == 0
    requires pd.off_vals[1] == 0
    requires pd.off_vals[2] == 0
    requires pd.off_vals[3] == 0
    requires pd.off_vals[4] == 1
    requires pd.off_vals[5] == 1
    requires pd.off_vals[6] == 1
    requires pd.off_vals[7] == 1
    requires pd.off_vals[8] == 2
    requires pd.off_vals[9] == 2
    requires pd.off_vals[10] == 2
    requires pd.off_vals[11] == 2
    requires pd.off_vals[12] == 3
    ensures pd.state == PD.LEDS_OFF
    // 0000111122223.
    ensures pd.off_vals[0] == 0
    ensures pd.off_vals[1] == 0
    ensures pd.off_vals[2] == 0
    ensures pd.off_vals[3] == 0
    ensures pd.off_vals[4] == 1
    ensures pd.off_vals[5] == 1
    ensures pd.off_vals[6] == 1
    ensures pd.off_vals[7] == 1
    ensures pd.off_vals[8] == 2
    ensures pd.off_vals[9] == 2
    ensures pd.off_vals[10] == 2
    ensures pd.off_vals[11] == 2
    ensures pd.off_vals[12] == 3
    // 1111000011100 in bool.
    ensures pd.punched[0] == true
    ensures pd.punched[1] == true
    ensures pd.punched[2] == true
    ensures pd.punched[3] == true
    ensures pd.punched[4] == false
    ensures pd.punched[5] == false
    ensures pd.punched[6] == false
    ensures pd.punched[7] == false
    ensures pd.punched[8] == true
    ensures pd.punched[9] == true
    ensures pd.punched[10] == true
    ensures pd.punched[11] == false
    ensures pd.punched[12] == false
  {
    // 5678432198760.
    var reading := new int[13];
    reading[0] := 5;
    reading[1] := 6;
    reading[2] := 7;
    reading[3] := 8;
    reading[4] := 4;
    reading[5] := 3;
    reading[6] := 2;
    reading[7] := 1;
    reading[8] := 9;
    reading[9] := 8;
    reading[10] := 7;
    reading[11] := 6;
    reading[12] := 0;
    pd.Tick(reading);
  }

  method {:test} Test_PD_04(pd: PD.PhotodiodeDriver)
    modifies pd, pd.off_vals, pd.punched
    requires pd.state == PD.LEDS_ON
    // 0000111122223.
    requires pd.off_vals[0] == 0
    requires pd.off_vals[1] == 0
    requires pd.off_vals[2] == 0
    requires pd.off_vals[3] == 0
    requires pd.off_vals[4] == 1
    requires pd.off_vals[5] == 1
    requires pd.off_vals[6] == 1
    requires pd.off_vals[7] == 1
    requires pd.off_vals[8] == 2
    requires pd.off_vals[9] == 2
    requires pd.off_vals[10] == 2
    requires pd.off_vals[11] == 2
    requires pd.off_vals[12] == 3
    ensures pd.state == PD.LEDS_OFF
    // 0000111122223.
    ensures pd.off_vals[0] == 0
    ensures pd.off_vals[1] == 0
    ensures pd.off_vals[2] == 0
    ensures pd.off_vals[3] == 0
    ensures pd.off_vals[4] == 1
    ensures pd.off_vals[5] == 1
    ensures pd.off_vals[6] == 1
    ensures pd.off_vals[7] == 1
    ensures pd.off_vals[8] == 2
    ensures pd.off_vals[9] == 2
    ensures pd.off_vals[10] == 2
    ensures pd.off_vals[11] == 2
    ensures pd.off_vals[12] == 3
    // 1110000000101 in bool.
    ensures pd.punched[0] == true
    ensures pd.punched[1] == true
    ensures pd.punched[2] == true
    ensures pd.punched[3] == false
    ensures pd.punched[4] == false
    ensures pd.punched[5] == false
    ensures pd.punched[6] == false
    ensures pd.punched[7] == false
    ensures pd.punched[8] == false
    ensures pd.punched[9] == false
    ensures pd.punched[10] == true
    ensures pd.punched[11] == false
    ensures pd.punched[12] == true
  {
    // 7654500056729.
    var reading := new int[13];
    reading[0] := 7;
    reading[1] := 6;
    reading[2] := 5;
    reading[3] := 4;
    reading[4] := 5;
    reading[5] := 0;
    reading[6] := 0;
    reading[7] := 0;
    reading[8] := 5;
    reading[9] := 6;
    reading[10] := 7;
    reading[11] := 2;
    reading[12] := 9;
    pd.Tick(reading);
  }

  method {:test} Test_PD_05(pd: PD.PhotodiodeDriver)
    modifies pd, pd.off_vals, pd.punched
    requires pd.state == PD.LEDS_ON
    // 0220333344410.
    requires pd.off_vals[0] == 0
    requires pd.off_vals[1] == 2
    requires pd.off_vals[2] == 2
    requires pd.off_vals[3] == 0
    requires pd.off_vals[4] == 3
    requires pd.off_vals[5] == 3
    requires pd.off_vals[6] == 3
    requires pd.off_vals[7] == 3
    requires pd.off_vals[8] == 4
    requires pd.off_vals[9] == 4
    requires pd.off_vals[10] == 4
    requires pd.off_vals[11] == 1
    requires pd.off_vals[12] == 0
    ensures pd.state == PD.LEDS_OFF
    // 0220333344410.
    ensures pd.off_vals[0] == 0
    ensures pd.off_vals[1] == 2
    ensures pd.off_vals[2] == 2
    ensures pd.off_vals[3] == 0
    ensures pd.off_vals[4] == 3
    ensures pd.off_vals[5] == 3
    ensures pd.off_vals[6] == 3
    ensures pd.off_vals[7] == 3
    ensures pd.off_vals[8] == 4
    ensures pd.off_vals[9] == 4
    ensures pd.off_vals[10] == 4
    ensures pd.off_vals[11] == 1
    ensures pd.off_vals[12] == 0
    // 1011000010010 in bool.
    ensures pd.punched[0] == true
    ensures pd.punched[1] == false
    ensures pd.punched[2] == true
    ensures pd.punched[3] == true
    ensures pd.punched[4] == false
    ensures pd.punched[5] == false
    ensures pd.punched[6] == false
    ensures pd.punched[7] == false
    ensures pd.punched[8] == true
    ensures pd.punched[9] == false
    ensures pd.punched[10] == false
    ensures pd.punched[11] == true
    ensures pd.punched[12] == false
  {
    // 5678432198760.
    var reading := new int[13];
    reading[0] := 5;
    reading[1] := 6;
    reading[2] := 7;
    reading[3] := 8;
    reading[4] := 4;
    reading[5] := 3;
    reading[6] := 2;
    reading[7] := 1;
    reading[8] := 9;
    reading[9] := 8;
    reading[10] := 7;
    reading[11] := 6;
    reading[12] := 0;
    pd.Tick(reading);
  }
}
