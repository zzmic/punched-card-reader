#include "PunchedCardReaderSimulator.h"
#include <bitset>
#include <iomanip>
#include <iostream>
#include <thread>

int main(int argc, char *argv[]) {
    bool binaryMode = false;
    std::string initialCardPath;

    if (argc > 3) {
        std::cerr << "Usage: " << argv[0] << " [--binary] [card_file_path]\n";
        return 1;
    }

    if (argc >= 2) {
        if (std::string(argv[1]) == "--binary") {
            binaryMode = true;
            if (argc == 3) {
                initialCardPath = argv[2];
            }
        }
        else if (argc == 2) {
            initialCardPath = argv[1];
        }
    }
    // Source - https://stackoverflow.com/a
    // Posted by rupello, modified by community. See post 'Timeline' for change
    // history Retrieved 2025-11-10, License - CC BY-SA 3.0
    initialCardPath.erase(std::remove_if(initialCardPath.begin(),
                                         initialCardPath.end(), ::isspace),
                          initialCardPath.end());

    PunchedCardReaderSimulator simulator(binaryMode);

    const auto runSimulation = [&](const std::string &cardFilePath) -> bool {
        try {
            std::array<std::uint32_t, CARD_COLUMNS>
                card{}; // Specify `{}` to zero-initialize the array.
            bool done = false;

            simulator.onCardDetected = [&cardFilePath]() {
                std::cout << "Card " << cardFilePath
                          << " detected in reader. Reading started.\n";
            };
            simulator.onColumnRead = [&](std::uint32_t data) {
                const size_t col = simulator.getCurrCol();
                if (col < CARD_COLUMNS) {
                    card[col] = data;
                    std::bitset<CARD_ROWS> bits(data);
                    std::string pad = (col + 1 < 10) ? " " : "";
                    if (simulator.getIsBinaryMode()) {
                        std::cout << "Col " << pad << col + 1 << "/"
                                  << CARD_COLUMNS << ": 0b" << bits.to_string()
                                  << "\n";
                    }
                    else {
                        std::cout << "Col " << pad << col + 1 << "/"
                                  << CARD_COLUMNS << ": 0x" << std::hex
                                  << std::uppercase << std::setw(3)
                                  << std::setfill('0') << data << std::dec
                                  << " (" << bits.to_string() << ")\n";
                    }
                }
            };
            simulator.onCardEjected = [&](bool isSuccessful) {
                std::cout << "Card ejected "
                          << (isSuccessful ? "successfully." : "with errors.")
                          << "\n";
                std::cout << "Ready for the next card.";
                done = true;
            };

            simulator.insertCard(cardFilePath);

            using namespace std::literals::chrono_literals;
            const auto TICK_RATE = 1ms;
            auto nextTick = std::chrono::steady_clock::now() + TICK_RATE;
            std::cout << "Simulation started: looping in 1ms (1kHz) ticks.\n";
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

    if (!initialCardPath.empty()) {
        runSimulation(initialCardPath);
    }

    std::string inputCardPath;
    while (true) {
        std::cout << "\nInsert next card file path (or \"done\" to exit): "
                  << std::flush;
        // Gracefully handle EOF (e.g., Ctrl+D).
        if (!std::getline(std::cin, inputCardPath)) {
            break;
        }
        // Skip empty inputs without exiting.
        if (inputCardPath.empty()) {
            continue;
        }
        // Terminate on "done".
        if (inputCardPath == "done") {
            break;
        }
        // Source - https://stackoverflow.com/a
        // Posted by rupello, modified by community. See post 'Timeline' for
        // change history Retrieved 2025-11-10, License - CC BY-SA 3.0
        inputCardPath.erase(std::remove_if(inputCardPath.begin(),
                                           inputCardPath.end(), ::isspace),
                            inputCardPath.end());
        runSimulation(inputCardPath);
    }

    std::cout << "Simulator ended.\n";
    return 0;
}
