#ifndef SIM_PUNCHEDCARDREADERSIMULATOR_H
#define SIM_PUNCHEDCARDREADERSIMULATOR_H

#include "PunchedCard.h"
#include <bitset>
#include <functional>
#include <iostream>
#include <memory>

// FSM States for the card processor.
enum class CardProcessorState { WAIT_FOR_CARD, WAIT_FOR_COLUMN, COLUMN_ENDED };

// FSM States for the photodiode driver.
enum class PhotodiodeState { LEDS_OFF, LEDS_ON };

class PunchedCardReaderSimulator {
  private:
    CardProcessorState currCPState;
    PhotodiodeState currPDState;
    std::unique_ptr<PunchedCard> currCard;
    size_t currCol;
    size_t sensorCol;
    uint8_t sensorPhase; // Sensor phase within a single LED on/off cycle, where
                         // 0 indicates to capture "illuminated" readings
                         // (`on_vals`) and 1 indicates to capture "ambient"
                         // readings (`off_vals`).
    std::bitset<13>
        prevPunched; // Previous boolean punched readings, where bit 0
                     // indicates card presence and bits 1--12
                     // indicate punched holes (rows 0--11 in `PunchedCard`).
    std::bitset<13> punched; // Current boolean punched readings, where the
                             // indexing is the same as `prevPunched`.
    bool ledCardPresence;    // Simulated output for the card‑presence indicator
                             // LED.
    bool ledSampling; // Simulated output for the sampling LED that flashes
                      // whenever a column (sampled) is being read.
    std::bitset<CARD_ROWS> lastColumnData;
    bool isBinaryMode;

  public:
    PunchedCardReaderSimulator(bool isBinaryMode = false);
    void tick(); // Function to advance the simulation FSM by one tick (discrete
                 // time step).
    void insertCard(const std::string &cardFilePath);
    void ejectCard();
    /* Getters for the LED states and other internal states. */
    CardProcessorState getCurrCPState() const { return currCPState; }
    PhotodiodeState getCurrPDState() const { return currPDState; }
    size_t getCurrCol() const { return currCol; }
    size_t getSensorCol() const { return sensorCol; }
    uint8_t getSensorPhase() const { return sensorPhase; }
    std::bitset<13> getPrevPunched() const { return prevPunched; }
    std::bitset<13> getPunched() const { return punched; }
    bool getCardPresenceLED() const { return ledCardPresence; }
    bool getSamplingLED() const { return ledSampling; }
    std::bitset<CARD_ROWS> getLastColumnData() const { return lastColumnData; }
    bool getIsBinaryMode() const { return isBinaryMode; }
    /* Callback functions for (external) event handling. */
    std::function<void()> onCardDetected;
    std::function<void(bool isSuccessful)> onCardEjected;
    std::function<void(std::uint32_t data)> onColumnRead;

  private:
    // Function to convert the last column data (in bitset) to a 32-bit unsigned
    // integer.
    std::uint32_t lastColumnDataToUint32() const;
    // Function to compute the punched data based on the simulated photodiode
    // input.
    void computePunched();
    // Function to update the card processor (FSM) state based on the new
    // `punched` data.
    void updateCPState();
};

#endif // SIM_PUNCHEDCARDREADERSIMULATOR_H
