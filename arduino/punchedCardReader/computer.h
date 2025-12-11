#ifndef COMPUTER_H
#define COMPUTER_H

/**
 * Mask for circular buffer indexing (length 128).
 */
const uint8_t BUFFER_MASK = 0x7F;

void sendByte(char b);

#endif // COMPUTER_H
