/**
 * Array mapping 8-bit values to characters.
 */
char eightBitToChar[256];

/**
 * Initialize the stream processor by setting up the character mapping.
 */
void initStreamProcessor() {
  for (int i = 0; i < 256; i++) {
    eightBitToChar[i] = unknownChar;
  }

  eightBitToChar[0x00] = ' ';
  eightBitToChar[0x01] = '1';
  eightBitToChar[0x02] = '2';
  eightBitToChar[0x03] = '3';
  eightBitToChar[0x04] = '4';
  eightBitToChar[0x05] = '5';
  eightBitToChar[0x06] = '6';
  eightBitToChar[0x07] = '7';
  eightBitToChar[0x08] = '8';
  eightBitToChar[0x09] = '`';
  eightBitToChar[0x0A] = ':';
  eightBitToChar[0x0B] = '#';
  eightBitToChar[0x0C] = '@';
  eightBitToChar[0x0D] = '\'';
  eightBitToChar[0x0E] = '=';
  eightBitToChar[0x0F] = '"';

  eightBitToChar[0x10] = '&';
  eightBitToChar[0x11] = 'A';
  eightBitToChar[0x12] = 'B';
  eightBitToChar[0x13] = 'C';
  eightBitToChar[0x14] = 'D';
  eightBitToChar[0x15] = 'E';
  eightBitToChar[0x16] = 'F';
  eightBitToChar[0x17] = 'G';
  eightBitToChar[0x18] = 'H';
  //eightBitToChar[0x19] =
  eightBitToChar[0x1A] = '[';
  eightBitToChar[0x1B] = '.';
  eightBitToChar[0x1C] = '<';
  eightBitToChar[0x1D] = '(';
  eightBitToChar[0x1E] = '+';
  eightBitToChar[0x1F] = '!';

  eightBitToChar[0x20] = '-';
  eightBitToChar[0x21] = 'J';
  eightBitToChar[0x22] = 'K';
  eightBitToChar[0x23] = 'L';
  eightBitToChar[0x24] = 'M';
  eightBitToChar[0x25] = 'N';
  eightBitToChar[0x26] = 'O';
  eightBitToChar[0x27] = 'P';
  eightBitToChar[0x28] = 'Q';
  //eightBitToChar[0x29] = '';
  eightBitToChar[0x2A] = ']';
  eightBitToChar[0x2B] = '$';
  eightBitToChar[0x2C] = '*';
  eightBitToChar[0x2D] = ')';
  eightBitToChar[0x2E] = ';';
  eightBitToChar[0x2F] = '^';

  eightBitToChar[0x30] = '|';
  eightBitToChar[0x31] = 'j';
  eightBitToChar[0x32] = 'k';
  eightBitToChar[0x33] = 'l';
  eightBitToChar[0x34] = 'm';
  eightBitToChar[0x35] = 'n';
  eightBitToChar[0x36] = 'o';
  eightBitToChar[0x37] = 'p';
  eightBitToChar[0x38] = 'q';
  // eightBitToChar[0x39] = '`';
  // eightBitToChar[0x3A] = ':';
  // eightBitToChar[0x3B] = '#';
  // eightBitToChar[0x3C] = '@';
  // eightBitToChar[0x3D] = '\'';
  // eightBitToChar[0x3E] = '=';
  // eightBitToChar[0x3F] = '"';

  eightBitToChar[0x40] = '0';
  eightBitToChar[0x41] = '/';
  eightBitToChar[0x42] = 'S';
  eightBitToChar[0x43] = 'T';
  eightBitToChar[0x44] = 'U';
  eightBitToChar[0x45] = 'V';
  eightBitToChar[0x46] = 'W';
  eightBitToChar[0x47] = 'X';
  eightBitToChar[0x48] = 'Y';
  //eightBitToChar[0x49] = '`';
  eightBitToChar[0x4A] = '\\';
  eightBitToChar[0x4B] = ',';
  eightBitToChar[0x4C] = '%';
  eightBitToChar[0x4D] = '_';
  eightBitToChar[0x4E] = '>';
  eightBitToChar[0x4F] = '?';

  eightBitToChar[0x50] = '{';
  eightBitToChar[0x51] = 'a';
  eightBitToChar[0x52] = 'b';
  eightBitToChar[0x53] = 'c';
  eightBitToChar[0x54] = 'd';
  eightBitToChar[0x55] = 'e';
  eightBitToChar[0x56] = 'f';
  eightBitToChar[0x57] = 'g';
  eightBitToChar[0x58] = 'h';
  // eightBitToChar[0x59] = '`';
  // eightBitToChar[0x5A] = ':';
  // eightBitToChar[0x5B] = '#';
  // eightBitToChar[0x5C] = '@';
  // eightBitToChar[0x5D] = '\'';
  // eightBitToChar[0x5E] = '=';
  // eightBitToChar[0x5F] = '"';

  eightBitToChar[0x60] = '}';
  eightBitToChar[0x61] = '~';
  eightBitToChar[0x62] = 's';
  eightBitToChar[0x63] = 't';
  eightBitToChar[0x64] = 'u';
  eightBitToChar[0x65] = 'v';
  eightBitToChar[0x66] = 'w';
  eightBitToChar[0x67] = 'x';
  eightBitToChar[0x68] = 'y';
  // eightBitToChar[0x69] = '`';
  // eightBitToChar[0x6A] = ':';
  // eightBitToChar[0x6B] = '#';
  // eightBitToChar[0x6C] = '@';
  // eightBitToChar[0x6D] = '\'';
  // eightBitToChar[0x6E] = '=';
  // eightBitToChar[0x6F] = '"';

  // eightBitToChar[0x70] = ' ';
  // eightBitToChar[0x71] = '1';
  // eightBitToChar[0x72] = '2';
  // eightBitToChar[0x73] = '3';
  // eightBitToChar[0x74] = '4';
  // eightBitToChar[0x75] = '5';
  // eightBitToChar[0x76] = '6';
  // eightBitToChar[0x77] = '7';
  // eightBitToChar[0x78] = '8';
  // eightBitToChar[0x79] = '`';
  // eightBitToChar[0x7A] = ':';
  // eightBitToChar[0x7B] = '#';
  // eightBitToChar[0x7C] = '@';
  // eightBitToChar[0x7D] = '\'';
  // eightBitToChar[0x7E] = '=';
  // eightBitToChar[0x7F] = '"';

  eightBitToChar[0x80] = '9';
  //eightBitToChar[0x81] = '1';
  // eightBitToChar[0x82] = '2';
  // eightBitToChar[0x83] = '3';
  // eightBitToChar[0x84] = '4';
  // eightBitToChar[0x85] = '5';
  // eightBitToChar[0x86] = '6';
  // eightBitToChar[0x87] = '7';
  // eightBitToChar[0x88] = '8';
  // eightBitToChar[0x89] = '`';
  // eightBitToChar[0x8A] = ':';
  // eightBitToChar[0x8B] = '#';
  // eightBitToChar[0x8C] = '@';
  // eightBitToChar[0x8D] = '\'';
  // eightBitToChar[0x8E] = '=';
  // eightBitToChar[0x8F] = '"';

  eightBitToChar[0x90] = 'I';
  // eightBitToChar[0x91] = '1';
  // eightBitToChar[0x92] = '2';
  // eightBitToChar[0x93] = '3';
  // eightBitToChar[0x94] = '4';
  // eightBitToChar[0x95] = '5';
  // eightBitToChar[0x96] = '6';
  // eightBitToChar[0x97] = '7';
  // eightBitToChar[0x98] = '8';
  // eightBitToChar[0x99] = '`';
  // eightBitToChar[0x9A] = ':';
  // eightBitToChar[0x9B] = '#';
  // eightBitToChar[0x9C] = '@';
  // eightBitToChar[0x9D] = '\'';
  // eightBitToChar[0x9E] = '=';
  // eightBitToChar[0x9F] = '"';

  eightBitToChar[0xA0] = 'R';
  // eightBitToChar[0xA1] = '1';
  // eightBitToChar[0xA2] = '2';
  // eightBitToChar[0xA3] = '3';
  // eightBitToChar[0xA4] = '4';
  // eightBitToChar[0xA5] = '5';
  // eightBitToChar[0xA6] = '6';
  // eightBitToChar[0xA7] = '7';
  // eightBitToChar[0xA8] = '8';
  // eightBitToChar[0xA9] = '`';
  // eightBitToChar[0xAA] = ':';
  // eightBitToChar[0xAB] = '#';
  // eightBitToChar[0xAC] = '@';
  // eightBitToChar[0xAD] = '\'';
  // eightBitToChar[0xAE] = '=';
  // eightBitToChar[0xAF] = '"';

  eightBitToChar[0xB0] = 'r';
  // eightBitToChar[0xB1] = '1';
  // eightBitToChar[0xB2] = '2';
  // eightBitToChar[0xB3] = '3';
  // eightBitToChar[0xB4] = '4';
  // eightBitToChar[0xB5] = '5';
  // eightBitToChar[0xB6] = '6';
  // eightBitToChar[0xB7] = '7';
  // eightBitToChar[0xB8] = '8';
  // eightBitToChar[0xB9] = '`';
  // eightBitToChar[0xBA] = ':';
  // eightBitToChar[0xBB] = '#';
  // eightBitToChar[0xBC] = '@';
  // eightBitToChar[0xBD] = '\'';
  // eightBitToChar[0xBE] = '=';
  // eightBitToChar[0xBF] = '"';

  eightBitToChar[0xC0] = 'Z';
  // eightBitToChar[0xC1] = '1';
  // eightBitToChar[0xC2] = '2';
  // eightBitToChar[0xC3] = '3';
  // eightBitToChar[0xC4] = '4';
  // eightBitToChar[0xC5] = '5';
  // eightBitToChar[0xC6] = '6';
  // eightBitToChar[0xC7] = '7';
  // eightBitToChar[0xC8] = '8';
  // eightBitToChar[0xC9] = '`';
  // eightBitToChar[0xCA] = ':';
  // eightBitToChar[0xCB] = '#';
  // eightBitToChar[0xCC] = '@';
  // eightBitToChar[0xCD] = '\'';
  // eightBitToChar[0xCE] = '=';
  // eightBitToChar[0xCF] = '"';

  eightBitToChar[0xD0] = 'i';
  // eightBitToChar[0xD1] = '1';
  // eightBitToChar[0xD2] = '2';
  // eightBitToChar[0xD3] = '3';
  // eightBitToChar[0xD4] = '4';
  // eightBitToChar[0xD5] = '5';
  // eightBitToChar[0xD6] = '6';
  // eightBitToChar[0xD7] = '7';
  // eightBitToChar[0xD8] = '8';
  eightBitToChar[0xD9] = '\0';
  // eightBitToChar[0xDA] = ':';
  // eightBitToChar[0xDB] = '#';
  // eightBitToChar[0xDC] = '@';
  // eightBitToChar[0xDD] = '\'';
  // eightBitToChar[0xDE] = '=';
  // eightBitToChar[0xDF] = '"';

  eightBitToChar[0xE0] = 'z';
  // eightBitToChar[0xE1] = '1';
  // eightBitToChar[0xE2] = '2';
  // eightBitToChar[0xE3] = '3';
  // eightBitToChar[0xE4] = '4';
  // eightBitToChar[0xE5] = '5';
  // eightBitToChar[0xE6] = '6';
  // eightBitToChar[0xE7] = '7';
  // eightBitToChar[0xE8] = '8';
  // eightBitToChar[0xE9] = '\0';
  // eightBitToChar[0xEA] = ':';
  // eightBitToChar[0xEB] = '#';
  // eightBitToChar[0xEC] = '@';
  // eightBitToChar[0xED] = '\'';
  // eightBitToChar[0xEE] = '=';
  // eightBitToChar[0xEF] = '"';

  // eightBitToChar[0xF0] = 'i';
  // eightBitToChar[0xF1] = '1';
  // eightBitToChar[0xF2] = '2';
  // eightBitToChar[0xF3] = '3';
  // eightBitToChar[0xF4] = '4';
  // eightBitToChar[0xF5] = '5';
  // eightBitToChar[0xF6] = '6';
  // eightBitToChar[0xF7] = '7';
  // eightBitToChar[0xF8] = '8';
  // eightBitToChar[0xE9] = '\0';
  // eightBitToChar[0xFA] = ':';
  // eightBitToChar[0xFB] = '#';
  // eightBitToChar[0xFC] = '@';
  // eightBitToChar[0xFD] = '\'';
  // eightBitToChar[0xFE] = '=';
  // eightBitToChar[0xFF] = '"';

}

/**
 * Convert a 16-bit column representation to its corresponding character.
 *
 * @param col The 16-bit column representation.
 * @return The corresponding character.
 */
char colToByte(uint16_t col) {
  if (col == 0b000100000100) {
    return ' ';
  }
  // Serial.print(col, BIN);
  // Serial.println("");
  uint8_t eightBitCode = (0b1 & col) << 7;
  for (int codeBitNum = 4; codeBitNum < 7; codeBitNum++) {
    int colBitNum = 15 - codeBitNum;
    if (col & (0b1 << colBitNum)) {
      eightBitCode += 0b1 << codeBitNum;
    }
  }
  col = col >> 1;
  for (uint8_t i = 8; i > 0; i--) {
    if (0b1 & col) {
      eightBitCode += i;
    }
    col = col >> 1;
  }
  return eightBitToChar[eightBitCode];
}

// StreamProcState updateStreamProcState(StreamProcState curState, uint16_t col, bool cardEnded) {
//   StreamProcState nextState = curState;
//   bool isBinary = isBinaryCol(col);

//   switch(curState) {
//     case s_TEXT:
//     if (cardEnded) {
//       sendByte('\n');
//     } else if (!cardEnded && !isBinary) {
//       sendByte(colToByte(col));
//     } else if (!cardEnded && isBinary) {
//       sendByte(colToByte(col));
//       nextState = s_BINARY;
//     }
//     break;

//     case s_BINARY:
//     if (cardEnded) {
//       nextState = s_TEXT;
//     } else if (!cardEnded && !isBinary) {
//       sendByte(colToByte(col));
//       nextState = s_TEXT;
//     } else if (!cardEnded && isBinary) {
//       sendByte(colToByte(col));
//     }
//     break;
//   }

//   return nextState;
// }

#ifndef TESTING
/**
 * Send a column's character representation.
 *
 * @param col The 16-bit column representation.
 */
void sendColumn(uint16_t col) {
  sendByte(colToByte(col));
}

/**
 * Send a newline character to indicate the end of a card.
 */
void sendCardEnd() {
  sendByte('\n');
}
#endif // TESTING
