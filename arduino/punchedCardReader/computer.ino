#ifndef TESTING
/**
 * Send/write a byte to the serial port.
 *
 * @param b The byte (in char) to send.
 */
void sendByte(char b) {
  //Serial.print(b);
  buffer[end] = b;
  end = (end + 1) & 0x7F;
}
#endif // TESTING
