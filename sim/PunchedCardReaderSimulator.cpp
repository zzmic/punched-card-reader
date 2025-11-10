#include "PunchedCardReaderSimulator.h"

PunchedCardReaderSimulator::PunchedCardReaderSimulator()
    : currentState(ReaderState::IDLE), currentColumn(0U),
      ledCardPresence(false), ledSampling(false), lastColumnData(0) {
    currentCard.reset();
}

void PunchedCardReaderSimulator::tick() {
    switch (currentState) {
    case ReaderState::IDLE:
        break;
    case ReaderState::CARD_DETECTED:
        onCardDetected();
        currentState = ReaderState::SAMPLING;
        break;
    case ReaderState::SAMPLING:
        ledSampling = true;
        if (currentCard) {
            lastColumnData = currentCard->getColumnData(currentColumn);
        }
        else {
            lastColumnData.reset();
        }
        currentState = ReaderState::COLUMN_READ;
        break;
    case ReaderState::COLUMN_READ:
        ledSampling = false;
        onColumnRead(lastColumnDataToUint32());
        currentState = ReaderState::ADVANCING_COLUMN;
        break;
    case ReaderState::ADVANCING_COLUMN:
        ++currentColumn;
        if (currentColumn >= CARD_COLUMNS) {
            currentState = ReaderState::EJECTING_CARD;
        }
        else {
            currentState = ReaderState::SAMPLING;
        }
        break;
    case ReaderState::EJECTING_CARD:
        ledCardPresence = false;
        currentCard.reset();
        onCardEjected(true);
        currentState = ReaderState::IDLE;
        break;
    }
}

void PunchedCardReaderSimulator::insertCard(SimulatedCard &card) {
    if (currentState == ReaderState::IDLE) {
        currentCard = std::make_unique<SimulatedCard>(card);
        ledCardPresence = true;
        currentColumn = 0U;
        currentState = ReaderState::CARD_DETECTED;
    }
}

void PunchedCardReaderSimulator::ejectCard() {
    ledCardPresence = false;
    if (currentState != ReaderState::IDLE) {
        if (onCardEjected) {
            onCardEjected(false);
        }
        currentCard.reset();
        currentState = ReaderState::IDLE;
    }
}

std::uint32_t PunchedCardReaderSimulator::lastColumnDataToUint32() const {
    return static_cast<std::uint32_t>(lastColumnData.to_ulong());
}
