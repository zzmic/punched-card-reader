/* Initialize the WDT peripheral */

void initWDT() {
  // TODO step 3 (prelab Qs6.1-6.2)
  R_WDT->WDTCR_b.CKS = 0b1000;
  R_WDT->WDTCR_b.TOPS = 0b10;
  R_WDT->WDTCR_b.RPSS = 0b11;
  R_WDT->WDTCR_b.RPES = 0b11;

  // Enable WDT when debugger is connected
  R_DEBUG->DBGSTOPCR_b.DBGSTOP_WDT = 0;
  R_WDT->WDTSR = 0; // clear watchdog status;

  // TODO step 3 (prelab Qs6.4-6.5): Make the watchdog trigger an interrupt
  // and use the ICU to connect it to the CPU
  // Make sure to call the correct CMSIS functions as well!
  R_WDT->WDTRCR_b.RSTIRQS = 1;
  R_ICU->IELSR[WDT_INT] = (0x025 << R_ICU_IELSR_IELS_Pos);

  NVIC_SetVector((IRQn_Type) WDT_INT, (uint32_t) &wdtISR); // set vector entry to our handler
  NVIC_SetPriority((IRQn_Type) WDT_INT, 15); // Priority lower than Serial (12)
  NVIC_EnableIRQ((IRQn_Type) WDT_INT);
}

/* pet the watchdog */
void petWDT() {
  R_WDT->WDTRR = 0;
  R_WDT->WDTRR = 0xFF;
}

/* ISR when WDT triggers */
void wdtISR() {
  // Serial.println("Watchdog triggered!");
  NVIC_SystemReset();
}
