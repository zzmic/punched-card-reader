include "Utilities.dfy"

/**
  * Module for controlling the stream processor.
  */
module StreamProcessorModule {
  import Utils = UtilitiesModule

  /**
    * Stream mode type(s) for the stream processor.
    */
  datatype StreamMode = TEXT | BINARY

  /**
    * Result type for the `HandleInput` method.
    */
  datatype HandleInputResult = HandleInputResult(
    output_char: char,
    output_bytes: seq<bv8>,
    output_ready: bool
  )

  /**
    * Class for controlling the stream processor.
    */
  class StreamProcessor {
    var stream_mode: StreamMode

    /**
      * Constructor that initializes the stream processor.
      */
    constructor()
      ensures stream_mode == TEXT
    {
      // Set default mode to `TEXT`.
      stream_mode := TEXT;
    }

    /**
      * Helper function to compute base^exp.
      *
      * @param base The base integer.
      * @param exp The exponent (natural number).
      * @returns The result of base raised to the power of exp.
      */
    function pow(base: int, exp: nat): int
      decreases exp
    {
      // Reference: https://stackoverflow.com/a/75557519.
      if exp == 0 then 1 else base * pow(base, exp - 1)
    }

    /**
      * Helper function to convert a sequence of booleans to an integer.
      *
      * @param s The sequence of booleans.
      * @returns The integer representation of the boolean sequence.
      */
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

    /**
      * Helper function to convert a column (array of length 12 booleans) to an integer.
      *
      * @param column The column represented as an array of length 12 booleans.
      * @returns The integer representation of the column.
      */
    function ColumnToInteger(column: Utils.arrayOfLength12<bool>): int
      reads column
      ensures 0 <= ColumnToInteger(column)
      ensures ColumnToInteger(column) < pow(2, 12)
    {
      BoolSeqToInteger(column[..12])
    }

    /**
      * Helper function to convert a column (array of length 12 booleans) to a sequence of 2 bytes.
      *
      * @param column The column represented as an array of length 12 booleans.
      * @returns The sequence of 2 bytes representing the column.
      */
    function ColumnToBytes(column: Utils.arrayOfLength12<bool>): seq<bv8>
      reads column
    {
      var val := ColumnToInteger(column);
      var b_high := (val / 256) as bv8;
      var b_low := (val % 256) as bv8;
      [b_high, b_low]
    }

    /**
      * Helper function to get the EBCDIC character for a given code.
      *
      * @param code The EBCDIC code as an integer.
      * @returns The corresponding EBCDIC character.
      */
    function GetEBCDICChar(code: int): char
    {
      // Reference 1: https://en.wikipedia.org/wiki/EBCDIC.
      // Reference 2: https://www.ibm.com/docs/en/i/7.1.0?topic=sets-invariant-character-set
      // The following covers the invariant character set ("invariant subset")
      // in which "the code point assignments do not change from code page to code page."
      match code

      case 0x40 => ' ' case 0x4B => '.' case 0x4C => '<' case 0x4D => '('
      case 0x4E => '+' case 0x50 => '&' case 0x5C => '*' case 0x5D => ')'
      case 0x5E => ';' case 0x60 => '-' case 0x61 => '/' case 0x6B => ','
      case 0x6C => '%' case 0x6D => '_' case 0x6E => '>' case 0x6F => '?'
      case 0x7A => ':' case 0x7D => '\'' case 0x7E => '=' case 0x7F => '"'

      case 0x81 => 'a' case 0x82 => 'b' case 0x83 => 'c' case 0x84 => 'd'
      case 0x85 => 'e' case 0x86 => 'f' case 0x87 => 'g' case 0x88 => 'h'
      case 0x89 => 'i' case 0x91 => 'j' case 0x92 => 'k' case 0x93 => 'l'
      case 0x94 => 'm' case 0x95 => 'n' case 0x96 => 'o' case 0x97 => 'p'
      case 0x98 => 'q' case 0x99 => 'r' case 0xA2 => 's' case 0xA3 => 't'
      case 0xA4 => 'u' case 0xA5 => 'v' case 0xA6 => 'w' case 0xA7 => 'x'
      case 0xA8 => 'y' case 0xA9 => 'z'

      case 0xC1 => 'A' case 0xC2 => 'B' case 0xC3 => 'C' case 0xC4 => 'D'
      case 0xC5 => 'E' case 0xC6 => 'F' case 0xC7 => 'G' case 0xC8 => 'H'
      case 0xC9 => 'I' case 0xD1 => 'J' case 0xD2 => 'K' case 0xD3 => 'L'
      case 0xD4 => 'M' case 0xD5 => 'N' case 0xD6 => 'O' case 0xD7 => 'P'
      case 0xD8 => 'Q' case 0xD9 => 'R' case 0xE2 => 'S' case 0xE3 => 'T'
      case 0xE4 => 'U' case 0xE5 => 'V' case 0xE6 => 'W' case 0xE7 => 'X'
      case 0xE8 => 'Y' case 0xE9 => 'Z'

      case 0xF0 => '0' case 0xF1 => '1' case 0xF2 => '2' case 0xF3 => '3'
      case 0xF4 => '4' case 0xF5 => '5' case 0xF6 => '6' case 0xF7 => '7'
      case 0xF8 => '8' case 0xF9 => '9'

      case _ => '?'
    }

    /**
      * Method to handle input based on the current stream mode, column data, and card ended flag.
      *
      * @param mode The current stream mode (`TEXT` or `BINARY`).
      * @param column The column represented as an array of length 12 booleans.
      * @param card_ended A boolean flag indicating whether the card has ended.
      * @returns A `HandleInputResult` containing the output character, output bytes, and output ready flag.
      */
    method HandleInput(mode: StreamMode, column: Utils.arrayOfLength12<bool>, card_ended: bool) returns (res : HandleInputResult)
      modifies this
      ensures (mode == TEXT) ==> (stream_mode == TEXT)
      ensures (mode == BINARY) ==> (stream_mode == BINARY)
      ensures (card_ended || !res.output_ready) ==> res.output_ready
      ensures (card_ended && mode == TEXT) ==> (res.output_char == '\n' && res.output_bytes == [])
      ensures (card_ended && mode == BINARY) ==> (res.output_bytes == [0x15 as bv8] && res.output_char == '?')
      ensures (!card_ended && mode == TEXT) ==> (res.output_char == GetEBCDICChar(ColumnToInteger(column)) && res.output_bytes == [])
      ensures (!card_ended && mode == BINARY) ==> (res.output_char == '?' && res.output_bytes == ColumnToBytes(column))
    {
      var output_char: char;
      var output_bytes: seq<bv8>;
      // var output_ready: bool;
      stream_mode := mode;

      if card_ended {
        match stream_mode {
          case TEXT =>
            output_char := '\n';
            output_bytes := [];
          case BINARY =>
            output_char := '?';
            output_bytes := [0x15 as bv8];
        }
      }
      else {
        match stream_mode {
          case TEXT =>
            var code := ColumnToInteger(column);
            output_char := GetEBCDICChar(code);
            output_bytes := [];
          case BINARY =>
            output_char := '?';
            output_bytes := ColumnToBytes(column);
        }
      }

      res := HandleInputResult(output_char, output_bytes, true);
    }
  }
}
