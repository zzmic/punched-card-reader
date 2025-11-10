#ifndef SIM_PUNCHEDCARDREADERSIMULATOR_H
#define SIM_PUNCHEDCARDREADERSIMULATOR_H

#include "SimulatedCard.h"
#include <bitset>
#include <functional>
#include <iostream>
#include <memory>
#include <random>
#include <vector>

enum class ReaderState {
    IDLE,
    CARD_DETECTED,
    SAMPLING,
    COLUMN_READ,
    ADVANCING_COLUMN,
    EJECTING_CARD
};

class PunchedCardReaderSimulator {
  private:
    ReaderState currentState;
    std::unique_ptr<SimulatedCard> currentCard;
    std::size_t currentColumn;
    bool ledCardPresence;
    bool ledSampling;
    std::bitset<CARD_ROWS> lastColumnData;

  public:
    PunchedCardReaderSimulator();
    // Function to advance the simulation FSM by one tick (discrete time step).
    void tick();
    void insertCard(SimulatedCard &card);
    void ejectCard();
    /* Getters for the LED states and other internal states. */
    ReaderState getState() const { return currentState; }
    std::size_t getCurrentColumn() const { return currentColumn; }
    bool getCardPresenceLED() const { return ledCardPresence; }
    bool getSamplingLED() const { return ledSampling; }
    std::bitset<CARD_ROWS> getLastColumnData() const { return lastColumnData; }
    /* Callbacks for event handling. */
    std::function<void()> onCardDetected;
    std::function<void(bool isSuccessful)> onCardEjected;
    std::function<void(std::uint32_t data)> onColumnRead;

  private:
    // Function to convert the last column data (in bitset) to a 32-bit integer.
    std::uint32_t lastColumnDataToUint32() const;
};

#endif // SIM_PUNCHEDCARDREADERSIMULATOR_H
