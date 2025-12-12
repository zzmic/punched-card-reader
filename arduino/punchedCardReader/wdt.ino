/**
 * Initialize the WDT peripheral.
 */
void initWDT() {
  // Watchdog timer has freq of 48MHz
  // R_WDT->WDTCR_b.CKS = 0b0001; // divide clock by 4
  R_WDT->WDTCR_b.CKS = 0b0100; // divide clock by 64
  R_WDT->WDTCR_b.TOPS = 0b00; // make timeout period 1024 cycles
  // 48000/(4*8192) = 0.73 KHz timeout period (we expect to pet it once per full cycle of our photodiode FSM, which is 1kHz)

  // Allow watchdog to be pet at any time 
  R_WDT->WDTCR_b.RPSS = 0b11;
  R_WDT->WDTCR_b.RPES = 0b11;

  // Enable WDT when debugger is connected
  R_DEBUG->DBGSTOPCR_b.DBGSTOP_WDT = 0;
  R_WDT->WDTSR = 0; // clear watchdog status;

  // Make the watchdog trigger an interrupt
  // and use the ICU to connect it to the CPU
  R_WDT->WDTRCR_b.RSTIRQS = 1;
  R_ICU->IELSR[WDT_INT] = (0x025 << R_ICU_IELSR_IELS_Pos);

  // Call the correct CMSIS functions as well!
  NVIC_SetVector((IRQn_Type) WDT_INT, (uint32_t) &wdtISR); // set vector entry to our handler
  NVIC_SetPriority((IRQn_Type) WDT_INT, 15); // Priority lower than Serial (12)
  NVIC_EnableIRQ((IRQn_Type) WDT_INT);
}

/**
 * Pet (reset) the watchdog timer to prevent it from triggering.
 */
void petWDT() {
  R_WDT->WDTRR = 0;
  R_WDT->WDTRR = 0xFF;
}

/**
 * Watchdog timer ISR that is called when the WDT triggers.
 */
void wdtISR() {
  // Serial.println("Watchdog triggered!");
  NVIC_SystemReset();
}
