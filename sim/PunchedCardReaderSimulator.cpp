#include "PunchedCardReaderSimulator.h"
#include "PunchedCard.h"

PunchedCardReaderSimulator::PunchedCardReaderSimulator(bool isBinaryMode)
    : currCPState(CardProcessorState::WAIT_FOR_CARD),
      currPDState(PhotodiodeState::LEDS_OFF), currCol(0U), sensorCol(0U),
      sensorPhase(0U), prevPunched(0), punched(0), ledCardPresence(false),
      ledSampling(false), lastColumnData(0), isBinaryMode(isBinaryMode) {
    currCard.reset();
}

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

std::uint32_t PunchedCardReaderSimulator::lastColumnDataToUint32() const {
    return static_cast<std::uint32_t>(lastColumnData.to_ulong());
}

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
        const auto colData = currCard->getColumnData(sensorCol);
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
        if (currCPState == CardProcessorState::WAIT_FOR_COLUMN) {
            ++sensorCol;
        }
    }
}

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
        if (allLow) {
            prevPunched = punched;
            currCPState = CardProcessorState::WAIT_FOR_COLUMN;
        }
        break;
    }
    }
}
