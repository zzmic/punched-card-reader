include "Utilities.dfy"
include "CardProcessor.dfy"

module CardProcessorTestsModule {
  import Utils = UtilitiesModule
  import CP = CardProcessorModule

  method {:test} Test_CP_01(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_CARD
    // 1111111111111 in bool.
    requires Utils.IsAllTrue(cp.prev_punched)
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 0000000000000 in bool.
    ensures Utils.IsAllFalse(cp.prev_punched)
  {
    // 0000000000000 in bool.
    var punched := Utils.SeqToArr13_bool([false,false,false,false,false,false,false,false,false,false,false,false,false]);
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_02(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_CARD
    // 1111111111111 in bool.
    requires Utils.IsAllTrue(cp.prev_punched)
    ensures cp.state == CP.WAIT_FOR_CARD
    // 1111111111111 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
  {
    // 1010101010101 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := false;
    punched[2] := true;
    punched[3] := false;
    punched[4] := true;
    punched[5] := false;
    punched[6] := true;
    punched[7] := false;
    punched[8] := true;
    punched[9] := false;
    punched[10] := true;
    punched[11] := false;
    punched[12] := true;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_03(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_CARD
    // 0000000000000 in bool.
    requires Utils.IsAllFalse(cp.prev_punched)
    ensures cp.state == CP.WAIT_FOR_CARD
    // 0000000000000 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
  {
    // 1010101010101 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := false;
    punched[2] := true;
    punched[3] := false;
    punched[4] := true;
    punched[5] := false;
    punched[6] := true;
    punched[7] := false;
    punched[8] := true;
    punched[9] := false;
    punched[10] := true;
    punched[11] := false;
    punched[12] := true;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_04(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    // Note that the following is not equivalent to `assert old(cp.prev_punched) == cp.prev_punched`
    // since it is testing for the coincidental case where `punched` is the same as `cp.prev_punched`.
    ensures cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
  {
    // 1110000001010 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := true;
    punched[2] := true;
    punched[3] := false;
    punched[4] := false;
    punched[5] := false;
    punched[6] := false;
    punched[7] := false;
    punched[8] := false;
    punched[9] := true;
    punched[10] := false;
    punched[11] := true;
    punched[12] := false;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_05(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001110 in bool.
    ensures cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,true,true,false]
  {
    // 1110000001110 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := true;
    punched[2] := true;
    punched[3] := false;
    punched[4] := false;
    punched[5] := false;
    punched[6] := false;
    punched[7] := false;
    punched[8] := false;
    punched[9] := true;
    punched[10] := true;
    punched[11] := true;
    punched[12] := false;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_06(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1110011001110 in bool.
    ensures cp.prev_punched[..] == [true,true,true,false,false,true,true,false,false,true,true,true,false]
  {
    // 1110011001110 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := true;
    punched[2] := true;
    punched[3] := false;
    punched[4] := false;
    punched[5] := true;
    punched[6] := true;
    punched[7] := false;
    punched[8] := false;
    punched[9] := true;
    punched[10] := true;
    punched[11] := true;
    punched[12] := false;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_07(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == true
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == false
    requires cp.prev_punched[7] == false
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == true
    requires cp.prev_punched[10] == false
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures forall i :: 0 <= i < 12 ==> res.column[i] == cp.prev_punched[i + 1]
  {
    // 1110000000010 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := true;
    punched[2] := true;
    punched[3] := false;
    punched[4] := false;
    punched[5] := false;
    punched[6] := false;
    punched[7] := false;
    punched[8] := false;
    punched[9] := false;
    punched[10] := false;
    punched[11] := true;
    punched[12] := false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_08(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == true
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == false
    requires cp.prev_punched[7] == false
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == true
    requires cp.prev_punched[10] == false
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures forall i :: 0 <= i < 12 ==> res.column[i] == cp.prev_punched[i + 1]
  {
    // 1100000000010 in bool.
    var punched := new bool[13];
    punched[0] := true;
    punched[1] := true;
    punched[2] := false;
    punched[3] := false;
    punched[4] := false;
    punched[5] := false;
    punched[6] := false;
    punched[7] := false;
    punched[8] := false;
    punched[9] := false;
    punched[10] := false;
    punched[11] := true;
    punched[12] := false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_09(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == true
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == false
    requires cp.prev_punched[7] == false
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == true
    requires cp.prev_punched[10] == false
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures forall i :: 0 <= i < 12 ==> res.column[i] == cp.prev_punched[i + 1]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13_bool([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_10(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000111111 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == true
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == false
    requires cp.prev_punched[7] == true
    requires cp.prev_punched[8] == true
    requires cp.prev_punched[9] == true
    requires cp.prev_punched[10] == true
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == true
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000111111 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000111111 in bool.
    ensures forall i :: 0 <= i < 12 ==> res.column[i] == cp.prev_punched[i + 1]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13_bool([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_11(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1000011100011 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == false
    requires cp.prev_punched[2] == false
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == true
    requires cp.prev_punched[6] == true
    requires cp.prev_punched[7] == true
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == false
    requires cp.prev_punched[10] == false
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == true
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1000011101011 in bool.
    ensures cp.prev_punched[..] == [true,false,false,false,false,true,true,true,false,true,false,true,true]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13_bool([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    assert punched[1] == false; // This is necessary to guide Dafny's verifier.
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_12(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == true
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == false
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == false
    requires cp.prev_punched[7] == false
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == true
    requires cp.prev_punched[10] == false
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.WAIT_FOR_CARD
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    ensures res.card_ended == true
  {
    // 1111111111111 in bool.
    var punched := Utils.SeqToArr13_bool([true,true,true,true,true,true,true,true,true,true,true,true,true]);
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_13(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == false
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == true
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == true
    requires cp.prev_punched[7] == true
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == false
    requires cp.prev_punched[10] == true
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
  {
    // 0001000000000 in bool.
    var punched := Utils.SeqToArr13_bool([false,false,false,true,false,false,false,false,false,false,false,false,false]);
    assert punched[3] == true; // This is necessary to guide Dafny's verifier.
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_14(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    requires cp.prev_punched[0] == true
    requires cp.prev_punched[1] == false
    requires cp.prev_punched[2] == true
    requires cp.prev_punched[3] == true
    requires cp.prev_punched[4] == false
    requires cp.prev_punched[5] == false
    requires cp.prev_punched[6] == true
    requires cp.prev_punched[7] == true
    requires cp.prev_punched[8] == false
    requires cp.prev_punched[9] == false
    requires cp.prev_punched[10] == true
    requires cp.prev_punched[11] == true
    requires cp.prev_punched[12] == false
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 0000000000000 in bool.
    ensures Utils.IsAllFalse(cp.prev_punched)
  {
    // 0000000000000 in bool.
    var punched := Utils.SeqToArr13_bool([false,false,false,false,false,false,false,false,false,false,false,false,false]);
    res := cp.ProcessEvent(punched);
  }
}
