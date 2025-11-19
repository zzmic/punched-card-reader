include "Utilities.dfy"
include "StreamProcessor.dfy"

module StreamProcessorTestsModule {
  import Utils = UtilitiesModule
  import SP = StreamProcessorModule

  method {:test} Test_SP_Mode_Switch(sp: SP.StreamProcessor, column: Utils.arrayOfLength12<bool>)
    modifies sp
  {
    var res1 := sp.HandleInput(SP.TEXT, column, false);
    assert sp.stream_mode == SP.TEXT;
    var res2 := sp.HandleInput(SP.BINARY, column, false);
    assert sp.stream_mode == SP.BINARY;
  }

  method {:test} Test_SP_Handle_CardEnded_TEXT(sp: SP.StreamProcessor, column: Utils.arrayOfLength12<bool>) returns (res: SP.HandleInputResult)
    modifies sp
    ensures sp.stream_mode == SP.TEXT
    ensures res.output_ready
    ensures res.output_char == '\n'
    ensures res.output_bytes == []
  {
    res := sp.HandleInput(SP.TEXT, column, true);
  }

  method {:test} Test_SP_Handle_CardEnded_BINARY(sp: SP.StreamProcessor, column: Utils.arrayOfLength12<bool>) returns (res: SP.HandleInputResult)
    modifies sp
    ensures sp.stream_mode == SP.BINARY
    ensures res.output_ready
    ensures res.output_char == '?'
    ensures res.output_bytes == [0x15 as bv8]
  {
    res := sp.HandleInput(SP.BINARY, column, true);
  }

  method Test_SP_Handle_Column_TEXT(sp: SP.StreamProcessor, column: Utils.arrayOfLength12<bool>) returns (res: SP.HandleInputResult)
    modifies sp
    ensures sp.stream_mode == SP.TEXT
    ensures res.output_ready
    ensures res.output_char == sp.GetEBCDICChar(sp.ColumnToInteger(column))
    ensures res.output_bytes == []
  {
    res := sp.HandleInput(SP.TEXT, column, false);
  }

  method {:test} Test_SP_Handle_Column_BINARY(sp: SP.StreamProcessor, column: Utils.arrayOfLength12<bool>) returns (res: SP.HandleInputResult)
    modifies sp
    ensures sp.stream_mode == SP.BINARY
    ensures res.output_ready
    ensures res.output_char == '?'
    ensures res.output_bytes == sp.ColumnToBytes(column)
  {
    res := sp.HandleInput(SP.BINARY, column, false);
  }

  method {:test} Test_SP_EBCDIC_char_whitespace_TEXT(sp: SP.StreamProcessor) returns (res: SP.HandleInputResult)
    modifies sp
    requires sp.stream_mode == SP.TEXT
  {
    // 0x40 = 0d64 -> 0b 0000 0100 0000 (padded to 12 bits).
    var column := Utils.SeqToArr12_bool([false, false, false, false, false, true, false, false, false, false, false, false]);
    res := sp.HandleInput(SP.TEXT, column, false);
    assert sp.stream_mode == SP.TEXT;
    assert res.output_ready;
    assert res.output_char == sp.GetEBCDICChar(sp.ColumnToInteger(column));
    assert res.output_bytes == [];
  }

  method {:test} Test_SP_EBCDIC_char_whitespace_BINARY(sp: SP.StreamProcessor) returns (res: SP.HandleInputResult)
    modifies sp
    requires sp.stream_mode == SP.BINARY
  {
    // 0x40 = 0d64 -> 0b 0000 0100 0000 (padded to 12 bits).
    var column := Utils.SeqToArr12_bool([false, false, false, false, false, true, false, false, false, false, false, false]);
    res := sp.HandleInput(SP.BINARY, column, false);
    assert sp.stream_mode == SP.BINARY;
    assert res.output_ready;
    assert res.output_char == '?';
    assert res.output_bytes == sp.ColumnToBytes(column);
  }

  method {:test} Test_SP_EBCDIC_char_newline_TEXT(sp: SP.StreamProcessor) returns (res: SP.HandleInputResult)
    modifies sp
    requires sp.stream_mode == SP.TEXT
  {
    // 0x15 = 0d21 -> 0b 0000 0001 0101 (padded to 12 bits).
    var column := Utils.SeqToArr12_bool([false, false, false, false, false, false, false, true, false, true, false, true]);
    res := sp.HandleInput(SP.TEXT, column, false);
    assert sp.stream_mode == SP.TEXT;
    assert res.output_ready;
    assert res.output_char == sp.GetEBCDICChar(sp.ColumnToInteger(column));
    assert res.output_bytes == [];
  }

  method {:test} Test_SP_EBCDIC_char_newline_BINARY(sp: SP.StreamProcessor) returns (res: SP.HandleInputResult)
    modifies sp
    requires sp.stream_mode == SP.BINARY
  {
    // 0x15 = 0d21 -> 0b 0000 0001 0101 (padded to 12 bits).
    var column := Utils.SeqToArr12_bool([false, false, false, false, false, false, false, true, false, true, false, true]);
    res := sp.HandleInput(SP.BINARY, column, false);
    assert sp.stream_mode == SP.BINARY;
    assert res.output_ready;
    assert res.output_char == '?';
    assert res.output_bytes == sp.ColumnToBytes(column);
  }
}
