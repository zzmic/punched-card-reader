include "Utilities.dfy"

module StreamProcessorModule {
  import CT = UtilitiesModule

  datatype StreamMode = TEXT | BINARY

  datatype HandleInputResult = HandleInputResult(
    output_char: char,
    output_bytes: seq<bv8>,
    output_ready: bool
  )

  class StreamProcessor {
    var mode: StreamMode

    constructor()
      ensures mode == TEXT
    {
      mode := TEXT;
    }

    // Reference: https://stackoverflow.com/a/75557519.
    function pow(base: int, exp: nat): int
      decreases exp
    {
      if exp == 0 then 1 else base * pow(base, exp - 1)
    }

    function BoolSeqToInteger(s: seq<bool>): int
      ensures 0 <= BoolSeqToInteger(s)
      ensures BoolSeqToInteger(s) < pow(2, |s|)
      decreases |s|
    {
      if |s| == 0 then
        0
      else
        (if s[0] then 1 else 0) + 2 * BoolSeqToInteger(s[1..])
    }

    function ColumnToInteger(col: CT.arrayOfLength12<bool>): int
      reads col
      ensures 0 <= ColumnToInteger(col)
      ensures ColumnToInteger(col) < pow(2, 12)
    {
      BoolSeqToInteger(col[..12])
    }


    function ColumnToBytes(col: CT.arrayOfLength12<bool>): seq<bv8>
      reads col
    {
      var val := ColumnToInteger(col);
      var b_high := (val / 256) as bv8;
      var b_low := (val % 256) as bv8;
      [b_high, b_low]
    }

    function GetEBCDICChar(code: int): char
    {
      match code
      case 0x40 => ' '

      case 0x81 => 'a'
      case 0x82 => 'b'
      case 0x83 => 'c'
      case 0x84 => 'd'
      case 0x85 => 'e'
      case 0x86 => 'f'
      case 0x87 => 'g'
      case 0x88 => 'h'
      case 0x89 => 'i'
      case 0x91 => 'j'
      case 0x92 => 'k'
      case 0x93 => 'l'
      case 0x94 => 'm'
      case 0x95 => 'n'
      case 0x96 => 'o'
      case 0x97 => 'p'
      case 0x98 => 'q'
      case 0x99 => 'r'
      case 0xA2 => 's'
      case 0xA3 => 't'
      case 0xA4 => 'u'
      case 0xA5 => 'v'
      case 0xA6 => 'w'
      case 0xA7 => 'x'
      case 0xA8 => 'y'
      case 0xA9 => 'z'

      case 0xC1 => 'A'
      case 0xC2 => 'B'
      case 0xC3 => 'C'
      case 0xC4 => 'D'
      case 0xC5 => 'E'
      case 0xC6 => 'F'
      case 0xC7 => 'G'
      case 0xC8 => 'H'
      case 0xC9 => 'I'
      case 0xD1 => 'J'
      case 0xD2 => 'K'
      case 0xD3 => 'L'
      case 0xD4 => 'M'
      case 0xD5 => 'N'
      case 0xD6 => 'O'
      case 0xD7 => 'P'
      case 0xD8 => 'Q'
      case 0xD9 => 'R'
      case 0xE2 => 'S'
      case 0xE3 => 'T'
      case 0xE4 => 'U'
      case 0xE5 => 'V'
      case 0xE6 => 'W'
      case 0xE7 => 'X'
      case 0xE8 => 'Y'
      case 0xE9 => 'Z'

      case 0xF0 => '0'
      case 0xF1 => '1'
      case 0xF2 => '2'
      case 0xF3 => '3'
      case 0xF4 => '4'
      case 0xF5 => '5'
      case 0xF6 => '6'
      case 0xF7 => '7'
      case 0xF8 => '8'
      case 0xF9 => '9'

      case _ => '?'
    }

    method HandleInput(mode_switch_is_binary: bool, column: CT.arrayOfLength12<bool>, card_ended: bool)
      returns (r : HandleInputResult)
      modifies this
    {
      var output_char: char;
      var output_bytes: seq<bv8>;
      var output_ready: bool;
      mode := if mode_switch_is_binary then BINARY else TEXT;
      if card_ended {
        output_ready := true;
        match mode {
          case TEXT =>
            output_char := '\n';
            output_bytes := [];
          case BINARY =>
            output_char := '?';
            output_bytes := [0x0A as bv8];
        }
      }
      else {
        output_ready := true;
        match mode {
          case TEXT =>
            var code := ColumnToInteger(column);
            output_char := GetEBCDICChar(code);
            output_bytes := [];
          case BINARY =>
            output_char := '?';
            output_bytes := ColumnToBytes(column);
        }
      }
      r := HandleInputResult(output_char, output_bytes, output_ready);
    }
  }
}
