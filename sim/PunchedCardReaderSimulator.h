#ifndef SIM_PUNCHEDCARDREADERSIMULATOR_H
#define SIM_PUNCHEDCARDREADERSIMULATOR_H

#include "SimulatedCard.h"
#include <bitset>
#include <functional>
#include <iostream>
#include <memory>

enum class CardProcessorState { WAIT_FOR_CARD, WAIT_FOR_COLUMN, COLUMN_ENDED };

enum class PhotodiodeState { LEDS_OFF, LEDS_ON };

class PunchedCardReaderSimulator {
  private:
    CardProcessorState currCPState;
    PhotodiodeState currPDState;
    std::unique_ptr<SimulatedCard> currCard;
    size_t currCol;
    size_t sensorCol;
    uint8_t sensorPhase;
    std::bitset<13> prevPunched;
    std::bitset<13> punched;
    bool ledCardPresence;
    bool ledSampling;
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
    // Function to convert the last column data (in bitset) to a 32-bit integer.
    std::uint32_t lastColumnDataToUint32() const;
    // Function to compute the punched data based on the current sensor state.
    void computePunched();
    // Function to update the card processor state.
    void updateCPState();
};

#endif // SIM_PUNCHEDCARDREADERSIMULATOR_H
