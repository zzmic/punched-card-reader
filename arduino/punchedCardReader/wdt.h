#ifndef WDT_H
#define WDT_H

/**
 * Watchdog timer interrupt interval in milliseconds.
 */
const unsigned int WDT_INT = 30;

void initWDT();
void petWDT();
void wdtISR();

#endif // WDT_H
