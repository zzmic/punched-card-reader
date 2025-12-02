const uint8_t binaryTag = 0b0001;
const uint8_t ebcdicTag = 0b0010;

char ebcdicToChar[256];

streamProcState curStreamProcState;

void initStreamProcessor() {
  curStreamProcState = s_TEXT;

  for (int i = 0; i < 256; i++) {
    ebcdicToChar[i] = unknownChar;
  }

  ebcdicToChar[0x00] = '\0';

  ebcdicToChar[0x40] = ' ';
  ebcdicToChar[0x4B] = '.';
  ebcdicToChar[0x4C] = '<';
  ebcdicToChar[0x4D] = '(';
  ebcdicToChar[0x4E] = '+';
  ebcdicToChar[0x4F] = '|';

  ebcdicToChar[0x50] = '&';
  ebcdicToChar[0x5C] = '*';
  ebcdicToChar[0x5D] = ')';
  ebcdicToChar[0x5E] = ';';

  ebcdicToChar[0x60] = '-';
  ebcdicToChar[0x61] = '/';
  ebcdicToChar[0x6B] = ',';
  ebcdicToChar[0x6C] = '%';
  ebcdicToChar[0x6D] = '_';
  ebcdicToChar[0x6E] = '>';

  ebcdicToChar[0x7A] = ':';
  ebcdicToChar[0x7D] = '\'';
  ebcdicToChar[0x7E] = '=';
  ebcdicToChar[0x7F] = '"';

  ebcdicToChar[0x81] = 'a';
  ebcdicToChar[0x82] = 'b';
  ebcdicToChar[0x83] = 'c';
  ebcdicToChar[0x84] = 'd';
  ebcdicToChar[0x85] = 'e';
  ebcdicToChar[0x86] = 'f';
  ebcdicToChar[0x87] = 'g';
  ebcdicToChar[0x88] = 'h';
  ebcdicToChar[0x89] = 'i';

  ebcdicToChar[0x91] = 'j';
  ebcdicToChar[0x92] = 'k';
  ebcdicToChar[0x93] = 'l';
  ebcdicToChar[0x94] = 'm';
  ebcdicToChar[0x95] = 'n';
  ebcdicToChar[0x96] = 'o';
  ebcdicToChar[0x97] = 'p';
  ebcdicToChar[0x98] = 'q';
  ebcdicToChar[0x99] = 'r';

  ebcdicToChar[0xA1] = '~';
  ebcdicToChar[0xA2] = 's';
  ebcdicToChar[0xA3] = 't';
  ebcdicToChar[0xA4] = 'u';
  ebcdicToChar[0xA5] = 'v';
  ebcdicToChar[0xA5] = 'q';
  ebcdicToChar[0xA7] = 'x';
  ebcdicToChar[0xA8] = 'y';
  ebcdicToChar[0xA9] = 'z';

  ebcdicToChar[0xB0] = '^';
  ebcdicToChar[0xBA] = '[';
  ebcdicToChar[0xBB] = ']';

  ebcdicToChar[0xC0] = '{';
  ebcdicToChar[0xC1] = 'A';
  ebcdicToChar[0xC2] = 'B';
  ebcdicToChar[0xC3] = 'C';
  ebcdicToChar[0xC4] = 'D';
  ebcdicToChar[0xC5] = 'E';
  ebcdicToChar[0xC6] = 'F';
  ebcdicToChar[0xC7] = 'G';
  ebcdicToChar[0xC8] = 'H';
  ebcdicToChar[0xC9] = 'I';

  ebcdicToChar[0xD0] = '}';
  ebcdicToChar[0xD1] = 'J';
  ebcdicToChar[0xD2] = 'K';
  ebcdicToChar[0xD3] = 'L';
  ebcdicToChar[0xD4] = 'M';
  ebcdicToChar[0xD5] = 'N';
  ebcdicToChar[0xD6] = 'O';
  ebcdicToChar[0xD7] = 'P';
  ebcdicToChar[0xD8] = 'Q';
  ebcdicToChar[0xD9] = 'R';

  ebcdicToChar[0xE0] = '\\';
  ebcdicToChar[0xE2] = 'S';
  ebcdicToChar[0xE3] = 'T';
  ebcdicToChar[0xE4] = 'U';
  ebcdicToChar[0xE5] = 'V';
  ebcdicToChar[0xE6] = 'W';
  ebcdicToChar[0xE7] = 'X';
  ebcdicToChar[0xE8] = 'Y';
  ebcdicToChar[0xE9] = 'Z';

  ebcdicToChar[0xF0] = '0';
  ebcdicToChar[0xF1] = '1';
  ebcdicToChar[0xF2] = '2';
  ebcdicToChar[0xF3] = '3';
  ebcdicToChar[0xF4] = '4';
  ebcdicToChar[0xF5] = '5';
  ebcdicToChar[0xF6] = '6';
  ebcdicToChar[0xF7] = '7';
  ebcdicToChar[0xF8] = '8';
  ebcdicToChar[0xF9] = '9';
}

bool isBinaryCol(uint16_t col) {
  return (col >> 8) == binaryTag;
}

char colToByte(uint16_t col) {
  uint8_t colData = col & 0b11111111;
  uint8_t typeTag = col >> 8;
  if (typeTag == binaryTag) {
    return (char)colData;
  } else if (typeTag == ebcdicTag) {
    return ebcdicToChar[colData];
  } else {
    return unknownChar;
  }
}

streamProcState updateStreamProcState(streamProcState curState, uint16_t col, bool cardEnded) {
  streamProcState nextState = curState;
  bool isBinary = isBinaryCol(col);

  switch(curState) {
    case s_TEXT:
    if (cardEnded) {
      sendByte('\n');
    } else if (!cardEnded && !isBinary) {
      sendByte(colToByte(col));
    } else if (!cardEnded && isBinary) {
      sendByte(colToByte(col));
      nextState = s_BINARY;
    }
    break;

    case s_BINARY:
    if (cardEnded) {
      nextState = s_TEXT;
    } else if (!cardEnded && !isBinary) {
      sendByte(colToByte(col));
      nextState = s_TEXT;
    } else if (!cardEnded && isBinary) {
      sendByte(colToByte(col));
    }
    break;
  }

  return nextState;
}

#ifndef TESTING
void sendColumn(uint16_t col) {
  curStreamProcState = updateStreamProcState(curStreamProcState, col, false);
}

void sendCardEnd() {
  curStreamProcState = updateStreamProcState(curStreamProcState, 0, true);
}
#endif // TESTING

