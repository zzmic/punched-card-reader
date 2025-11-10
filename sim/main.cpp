#include "PunchedCardReaderSimulator.h"
#include <thread>

void printCard(const std::array<std::uint32_t, CARD_COLUMNS> &card) {
    std::cout << "Punched Card:\n";
    std::cout << std::string(CARD_COLUMNS, '-') << "\n";
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
    std::cout << std::string(CARD_COLUMNS, '-') << "\n";
}

int main(int argc, char *argv[]) {
    if (argc > 2) {
        std::cerr << "Usage: " << argv[0] << " <path_to_card_file>\n";
        return 1;
    }

    PunchedCardReaderSimulator simulator;

    const auto runSimulation = [&](const std::string &cardFilePath) -> bool {
        try {
            std::array<std::uint32_t, CARD_COLUMNS> card{};
            bool done = false;

            simulator.onCardDetected = []() {
                std::cout << "Card detected in reader. Reading started.\n";
            };
            simulator.onColumnRead = [&](std::uint32_t data) {
                const std::size_t col = simulator.getCurrentColumn();
                if (col < CARD_COLUMNS) {
                    card[col] = data;
                }
            };
            simulator.onCardEjected = [&](bool isSuccessful) {
                std::cout << "Card ejected "
                          << (isSuccessful ? "successfully." : "with errors.")
                          << "\n";
                printCard(card);
                std::cout << "Ready for the next card.\n";
                done = true;
            };

            simulator.insertCard(cardFilePath);

            using namespace std::literals::chrono_literals;
            const auto TICK_RATE = 1ms;
            auto nextTick = std::chrono::steady_clock::now() + TICK_RATE;
            std::cout << "Simulation started. Running 1kHz loop.\n";
            while (!done) {
                simulator.tick();
                std::this_thread::sleep_until(nextTick);
                nextTick += TICK_RATE;
            }
            return true;
        } catch (const std::exception &e) {
            std::cerr << "Error processing card: " << e.what() << "\n";
            return false;
        }
    };

    if (argc == 2) {
        runSimulation(argv[1]);
    }

    std::string input;
    while (true) {
        std::cout << "\nInsert next card file path (or \"done\" to exit): "
                  << std::flush;
        if (!std::getline(std::cin, input)) {
            break;
        }
        if (input.empty()) {
            continue;
        }
        if (input == "done") {
            break;
        }
        runSimulation(input);
    }

    std::cout << "Simulator ended.\n";
    return 0;
}
