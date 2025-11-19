include "Utilities.dfy"
include "PhotodiodeDriver.dfy"

module PhotodiodeDriverTestsModule {
  import Utils = UtilitiesModule
  import PD = PhotodiodeDriverModule

  method {:test} Test_PD_Tick_FSM(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    modifies pd, pd.off_vals, pd.punched
    ensures old(pd.state) == PD.LEDS_OFF ==> pd.state == PD.LEDS_ON
    ensures old(pd.state) == PD.LEDS_ON ==> pd.state == PD.LEDS_OFF
  {
    var start_state := pd.state;
    pd.Tick(reading);
  }

  method {:test} Test_PD_LEDS_Off_Behavior(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    requires pd.state == PD.LEDS_OFF
    modifies pd, pd.off_vals, pd.punched
    ensures pd.state == PD.LEDS_ON
    ensures forall i :: 0 <= i < 13 ==> pd.off_vals[i] == reading[i]
    ensures pd.punched[..] == old(pd.punched)[..]
  {
    var old_punched := pd.punched;
    pd.Tick(reading);
  }

  method {:test} Test_PD_LEDS_On_Behavior(pd: PD.PhotodiodeDriver, reading: Utils.arrayOfLength13<int>)
    requires pd.state == PD.LEDS_ON
    modifies pd, pd.off_vals, pd.punched
    ensures pd.state == PD.LEDS_OFF
    ensures forall i :: 0 <= i < 13 ==> pd.punched[i] == (reading[i] - old(pd.off_vals[i]) > pd.THRESHOLD)
    ensures pd.off_vals[..] == old(pd.off_vals)[..]
  {
    var old_off_vals := pd.off_vals;
    pd.Tick(reading);
  }

  method {:test} Test_PD_01(pd: PD.PhotodiodeDriver)
    modifies pd, pd.off_vals, pd.punched
    requires pd.state == PD.LEDS_OFF
    // 0000000000000.
    requires Utils.IsAllZero(pd.off_vals)
  {
    // 0000111122223.
    var reading := Utils.SeqToArr13_int([0,0,0,0,1,1,1,1,2,2,2,2,3]);
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
  {
    // 0220333344410.
    var reading := Utils.SeqToArr13_int([0,2,2,0,3,3,3,3,4,4,4,1,0]);
    pd.Tick(reading);

    assert pd.state == PD.LEDS_ON;
    // 0220333344410.
    assert pd.off_vals[..] == reading[..];
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
  {
    // 5678432198760.
    var reading := Utils.SeqToArr13_int([5,6,7,8,4,3,2,1,9,8,7,6,0]);
    pd.Tick(reading);

    assert pd.state == PD.LEDS_OFF;
    // 0000111122223.
    assert pd.off_vals[..] == old(pd.off_vals)[..];
    // 1111000011100 in bool.
    assert pd.punched[..] == [true,true,true,true,false,false,false,false,true,true,true,false,false];
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
  {
    // 7654500056729.
    var reading := Utils.SeqToArr13_int([7,6,5,4,5,0,0,0,5,6,7,2,9]);
    pd.Tick(reading);

    assert pd.state == PD.LEDS_OFF;
    // 0000111122223.
    assert pd.off_vals[..] == old(pd.off_vals)[..];
    // 1110000000101 in bool.
    assert pd.punched[..] == [true,true,true,false,false,false,false,false,false,false,true,false,true];
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
  {
    // 5678432198760.
    var reading := Utils.SeqToArr13_int([5,6,7,8,4,3,2,1,9,8,7,6,0]);
    pd.Tick(reading);

    assert pd.state == PD.LEDS_OFF;
    // 0220333344410.
    assert pd.off_vals[..] == old(pd.off_vals)[..];
    // 1011000010010 in bool.
    assert pd.punched[..] == [true,false,true,true,false,false,false,false,true,false,false,true,false];
  }
}
