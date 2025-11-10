#include "PunchedCardReaderSimulator.h"

PunchedCardReaderSimulator::PunchedCardReaderSimulator(bool isBinaryMode)
    : currentState(ReaderState::IDLE), currentColumn(0U),
      ledCardPresence(false), ledSampling(false), lastColumnData(0),
      isBinaryMode(isBinaryMode) {
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
        // For each column, output the bitset to stdout.
        for (std::size_t row = 0; row < CARD_ROWS; ++row) {
            if (isBinaryMode) {
                std::cout << (lastColumnData.test(row) ? '1' : '0');
            }
            else {
                std::cout << (lastColumnData.test(row) ? 'P' : '.');
            }
        }
        std::cout << "\n";
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

void PunchedCardReaderSimulator::insertCard(const std::string &cardFilePath) {
    if (currentState == ReaderState::IDLE) {
        currentCard = std::make_unique<SimulatedCard>(cardFilePath);
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
