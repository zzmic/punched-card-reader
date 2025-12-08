#ifndef TESTING
/**
 * Send/write a byte to the serial port.
 *
 * @param b The byte (in char) to send.
 */
void sendByte(char b) {
  Serial.write(b);
}
#endif // TESTING
