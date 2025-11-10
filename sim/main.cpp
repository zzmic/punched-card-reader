#include "PunchedCardReaderSimulator.h"
#include <array>
#include <iostream>
#include <thread>

void printCard(const std::array<std::uint32_t, CARD_COLUMNS> &card) {
    std::cout << "Punched Card:\n";
    std::cout << std::string(80, '-') << "\n";
    for (std::size_t row = 0; row < CARD_ROWS; ++row) {
        for (std::size_t col = 0; col < CARD_COLUMNS; ++col) {
            const std::uint32_t columnData = card[col];
            if (((columnData >> row) & 1U) != 0U) {
                std::cout << "P";
            }
            else {
                std::cout << ".";
            }
        }
        std::cout << "\n";
    }
    std::cout << std::string(80, '-') << "\n";
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <path_to_punched_card_file>\n";
        return 1;
    }

    const std::string cardFilePath = argv[1];
    try {
        SimulatedCard simulatedCard(cardFilePath);
        PunchedCardReaderSimulator simulator;
        std::array<std::uint32_t, CARD_COLUMNS> card{};
        bool done = false;
        simulator.onCardDetected = []() {
            std::cout << "Card detected in reader: Reading started.\n";
        };
        simulator.onColumnRead = [&](std::uint32_t data) {
            const std::size_t col = simulator.getCurrentColumn();
            if (col < CARD_COLUMNS) {
                card[col] = data;
            }
        };
        simulator.onCardEjected = [&](bool isSuccessful) {
            std::cout << "Card ejected "
                      << (isSuccessful ? "successfully.\n" : "with errors.\n");
            printCard(card);
            // std::cout << "Ready for next card.\n";
            done = true;
        };
        simulator.insertCard(simulatedCard);
        using namespace std::literals::chrono_literals;
        const auto tick_rate = 1ms;
        auto next_tick = std::chrono::steady_clock::now() + tick_rate;
        std::cout << " Simulation started. Running 1kHz loop." << "\n";
        while (!done) {
            simulator.tick();
            std::this_thread::sleep_until(next_tick);
            next_tick += tick_rate;
        }
    } catch (const std::exception &e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
