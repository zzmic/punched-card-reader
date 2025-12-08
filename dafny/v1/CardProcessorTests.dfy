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
    var punched := Utils.SeqToArr13<bool>([false,false,false,false,false,false,false,false,false,false,false,false,false]);
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
    var punched := Utils.SeqToArr13<bool>([true,false,true,false,true,false,true,false,true,false,true,false,true]);
    assert punched[0];
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
    var punched := Utils.SeqToArr13<bool>([true,false,true,false,true,false,true,false,true,false,true,false,true]);
    assert punched[0];
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_04(cp: CP.CardProcessor)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    // Note: the following is not equivalent to `assert old(cp.prev_punched) == cp.prev_punched`
    // since it is testing for the coincidental case where `punched` is the same as `cp.prev_punched`.
    ensures cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
  {
    // 1110000001010 in bool.
    var punched := Utils.SeqToArr13<bool>([true,true,true,false,false,false,false,false,false,true,false,true,false]);
    assert punched[3] == false;
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
    var punched := Utils.SeqToArr13<bool>([true,true,true,false,false,false,false,false,false,true,true,true,false]);
    assert punched[3] == false;
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
    var punched := Utils.SeqToArr13<bool>([true,true,true,false,false,true,true,false,false,true,true,true,false]);
    assert punched[3] == false;
    var res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_07(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures res.column[..] == cp.prev_punched[1..13]
  {
    // 1110000000010 in bool.
    var punched := Utils.SeqToArr13<bool>([true,true,false,false,false,false,false,false,false,false,false,true,false]);
    assert punched[2] == false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_08(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures res.column[..] == cp.prev_punched[1..13]
  {
    // 1100000000010 in bool.
    var punched := Utils.SeqToArr13<bool>([true,true,false,false,false,false,false,false,false,false,false,true,false]);
    assert punched[2] == false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_09(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000001010 in bool.
    ensures res.column[..] == cp.prev_punched[1..13]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13<bool>([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    assert punched[1] == false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_10(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000111111 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,true,true,true,true,true,true]
    ensures cp.state == CP.COLUMN_ENDED
    // 1110000111111 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    // 110000111111 in bool.
    ensures res.column[..] == cp.prev_punched[1..13]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13<bool>([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    assert punched[1] == false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_11(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1000011100011 in bool.
    requires cp.prev_punched[..] == [true,false,false,false,false,true,true,true,false,false,false,true,true]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 1000011101011 in bool.
    ensures cp.prev_punched[..] == [true,false,false,false,false,true,true,true,false,true,false,true,true]
  {
    // 1000011101011 in bool.
    var punched := Utils.SeqToArr13<bool>([true,false,false,false,false,true,true,true,false,true,false,true,true]);
    assert punched[1] == false;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_12(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.WAIT_FOR_COLUMN
    // 1110000001010 in bool.
    requires cp.prev_punched[..] == [true,true,true,false,false,false,false,false,false,true,false,true,false]
    ensures cp.state == CP.WAIT_FOR_CARD
    // 1110000001010 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
    ensures res.card_ended == true
  {
    // 1111111111111 in bool.
    var punched := Utils.SeqToArr13<bool>([true,true,true,true,true,true,true,true,true,true,true,true,true]);
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_13(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    requires cp.prev_punched[..] == [true,false,true,true,false,false,true,true,false,false,true,true,false]
    ensures cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    ensures old(cp.prev_punched)[..] == cp.prev_punched[..]
  {
    // 0001000000000 in bool.
    var punched := Utils.SeqToArr13<bool>([false,false,false,true,false,false,false,false,false,false,false,false,false]);
    assert punched[3] == true;
    res := cp.ProcessEvent(punched);
  }

  method {:test} Test_CP_14(cp: CP.CardProcessor) returns (res: CP.ProcessEventResult)
    modifies cp, cp.prev_punched
    requires cp.state == CP.COLUMN_ENDED
    // 1011001100110 in bool.
    requires cp.prev_punched[..] == [true,false,true,true,false,false,true,true,false,false,true,true,false]
    ensures cp.state == CP.WAIT_FOR_COLUMN
    // 0000000000000 in bool.
    ensures Utils.IsAllFalse(cp.prev_punched)
  {
    // 0000000000000 in bool.
    var punched := Utils.SeqToArr13<bool>([false,false,false,false,false,false,false,false,false,false,false,false,false]);
    res := cp.ProcessEvent(punched);
  }
}
