#include "PunchedCardReaderSimulator.h"
#include "PunchedCard.h"

/**
 * Constructor that initializes the punched card reader simulator.
 */
PunchedCardReaderSimulator::PunchedCardReaderSimulator(bool isBinaryMode)
    : currCPState(CardProcessorState::WAIT_FOR_CARD),
      currPDState(PhotodiodeState::LEDS_OFF), currCol(0U), sensorCol(0U),
      sensorPhase(0U), prevPunched(0), punched(0), ledCardPresence(false),
      ledSampling(false), lastColumnData(0), isBinaryMode(isBinaryMode) {
    currCard.reset();
}

/**
 * Simulate a clock tick (next-state action) for the punched card reader.
 *
 * This method alternates the photodiode state between `LEDS_OFF` and `LEDS_ON`,
 * computes the punched data, and updates the card processor state accordingly.
 */
void PunchedCardReaderSimulator::tick() {
    if (currPDState == PhotodiodeState::LEDS_OFF) {
        ledSampling = false;
        currPDState = PhotodiodeState::LEDS_ON;
    }
    else {
        ledSampling = true;
        computePunched();
        updateCPState();
        currPDState = PhotodiodeState::LEDS_OFF;
    }
}

/**
 * Insert a punched card into the reader from the specified file.
 *
 * @param cardFilePath The path to the file containing punched card data.
 */
void PunchedCardReaderSimulator::insertCard(const std::string &cardFilePath) {
    if (currCard) {
        return;
    }
    currCPState = CardProcessorState::WAIT_FOR_CARD;
    currPDState = PhotodiodeState::LEDS_OFF;
    currCard = std::make_unique<PunchedCard>(cardFilePath);
    currCol = 0U;
    sensorCol = 0U;
    sensorPhase = 0U;
    prevPunched.reset();
    punched.reset();
    ledCardPresence = false;
    ledSampling = false;
}

/**
 * Eject the currently inserted punched card from the reader.
 */
void PunchedCardReaderSimulator::ejectCard() {
    if (!currCard) {
        return;
    }
    if (onCardEjected) {
        onCardEjected(false);
    }
    currCPState = CardProcessorState::WAIT_FOR_CARD;
    currPDState = PhotodiodeState::LEDS_OFF;
    currCard.reset();
    currCol = 0U;
    sensorCol = 0U;
    sensorPhase = 0U;
    prevPunched.reset();
    punched.reset();
    ledCardPresence = false;
    ledSampling = false;
}

/**
 * Convert the last column data to a 32-bit unsigned integer.
 *
 * @return The last column data as a `uint32_t`.
 */
std::uint32_t PunchedCardReaderSimulator::lastColumnDataToUint32() const {
    return static_cast<std::uint32_t>(lastColumnData.to_ulong());
}

/**
 * Compute the punched data based on the current sensor column and phase.
 */
void PunchedCardReaderSimulator::computePunched() {
    if (!currCard) {
        punched.reset();
        return;
    }
    if (sensorCol >= CARD_COLUMNS) {
        punched.set();
        return;
    }
    if (sensorPhase == 0U) {
        punched.set(0, true);
        const auto colData = currCard->getColData(sensorCol);
        for (size_t i = 0; i < CARD_ROWS; ++i) {
            punched.set(i + 1, colData.test(i));
        }
        sensorPhase = 1U;
    }
    else {
        punched.set(0, false);
        for (size_t i = 0; i < CARD_ROWS; ++i) {
            punched.set(i + 1, false);
        }
        sensorPhase = 0U;
        // If the card processor is actively reading columns (i.e., in the
        // `WAIT_FOR_COLUMN` state), advance the sensor column to move to the
        // next column.
        // Otherwise, keep the sensor column unchanged.
        if (currCPState == CardProcessorState::WAIT_FOR_COLUMN) {
            ++sensorCol;
        }
    }
}

/**
 * Update the card processor state based on the current punched data and card
 * presence.
 */
void PunchedCardReaderSimulator::updateCPState() {
    if (currCard && punched.all()) {
        if (onCardEjected) {
            onCardEjected(true);
        }
        currCPState = CardProcessorState::WAIT_FOR_CARD;
        currPDState = PhotodiodeState::LEDS_OFF;
        currCard.reset();
        currCol = 0U;
        sensorCol = 0U;
        sensorPhase = 0U;
        prevPunched.reset();
        punched.reset();
        ledCardPresence = false;
        return;
    }
    switch (currCPState) {
    case CardProcessorState::WAIT_FOR_CARD: {
        if (punched.test(0)) {
            if (onCardDetected) {
                onCardDetected();
            }
            currCPState = CardProcessorState::WAIT_FOR_COLUMN;
            ledCardPresence = true;
            prevPunched = punched;
        }
        break;
    }
    case CardProcessorState::WAIT_FOR_COLUMN: {
        bool fallingEdge = false;
        for (size_t i = 0; i <= CARD_ROWS; ++i) {
            if (prevPunched.test(i) && !punched.test(i)) {
                fallingEdge = true;
                break;
            }
        }
        if (fallingEdge) {
            for (size_t i = 0; i < CARD_ROWS; ++i) {
                lastColumnData.set(i, prevPunched.test(i + 1));
            }
            if (onColumnRead) {
                onColumnRead(lastColumnDataToUint32());
            }
            ++currCol;
            currCPState = CardProcessorState::COLUMN_ENDED;
        }
        else {
            prevPunched = punched;
        }
        break;
    }
    case CardProcessorState::COLUMN_ENDED: {
        bool allLow = true;
        for (size_t i = 0; i <= CARD_ROWS; ++i) {
            if (punched.test(i)) {
                allLow = false;
                break;
            }
        }
        // If all bits are low, which indicates the end of the column,
        // synchronize `prevPunched` with the current all-low `punched`
        // and transition back to `WAIT_FOR_COLUMN` state.
        // Otherwise, remain in `COLUMN_ENDED` state.
        if (allLow) {
            prevPunched = punched;
            currCPState = CardProcessorState::WAIT_FOR_COLUMN;
        }
        break;
    }
    }
}
