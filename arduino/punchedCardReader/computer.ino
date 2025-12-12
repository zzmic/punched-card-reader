#ifndef TESTING
/**
 * Sends a byte to the serial buffer.
 *
 * The function writes the byte `b` into the end of a circular buffer.
 * The `end` index is then incremented, wrapping around using a bitwise AND
 * with `BUFFER_MASK` to ensure that it stays within the bounds of the buffer length (128 bytes).
 *
 * @param b The byte (in char) to send.
 */
void sendByte(char b) {
  //Serial.print(b);
  buffer[end] = b;
  end = (end + 1) & BUFFER_MASK;
}
#endif // TESTING
