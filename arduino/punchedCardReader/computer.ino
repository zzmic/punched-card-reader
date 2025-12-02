#ifdef PRODUCTION
void sendByte(char b) {
  Serial.write(b);
}
#endif
