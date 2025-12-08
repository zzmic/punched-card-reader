#include "PunchedCard.h"
#include <fstream>
#include <iostream>

/**
 * Constructor that reads punched card data from a specified file.
 *
 * @param filePath The path to the file containing punched card data.
 */
PunchedCard::PunchedCard(const std::string &filePath) {
    for (auto &col : cardData) {
        col.reset();
    }

    std::ifstream file(filePath);
    if (!file.is_open()) {
        throw std::runtime_error("Failed to open file: " + filePath);
    }

    std::vector<std::string> lines;
    std::string line;
    while (std::getline(file, line)) {
        lines.push_back(line);
    }

    if (lines.size() != CARD_ROWS) {
        std::cerr << "Warning: Expected " << CARD_ROWS << " rows, but got "
                  << lines.size() << " rows.\n";
    }

    // Iterate over each column and row to populate the `cardData` matrix.
    // Treat white spaces (' ') and periods ('.') as no punch and anything else
    // as a punch.
    for (size_t col = 0; col < CARD_COLUMNS; ++col) {
        for (size_t row = 0; row < CARD_ROWS; ++row) {
            if (row < lines.size() && col < lines[row].size()) {
                if (lines[row][col] != ' ' && lines[row][col] != '.') {
                    cardData[col].set(row);
                }
            }
        }
    }
}

/**
 * Retrieve the punched data for a specific column.
 *
 * @param colIdx The index of the column (0 to 79).
 * @return A bitset representing the punched data for the specified column.
 */
std::bitset<CARD_ROWS> PunchedCard::getColData(size_t colIdx) const {
    if (colIdx >= CARD_COLUMNS) {
        throw std::out_of_range("Column index out of range: " +
                                std::to_string(colIdx));
    }
    return cardData[colIdx];
}
