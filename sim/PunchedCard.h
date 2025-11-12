#ifndef SIM_PUNCHEDCARD_H
#define SIM_PUNCHEDCARD_H

#include <array>
#include <bitset>
#include <string>
#include <vector>

// Constants defining the dimensions of an IBM 12-row/80-column punched card.
constexpr size_t CARD_COLUMNS = 80;
constexpr size_t CARD_ROWS = 12;

class PunchedCard {
  public:
    PunchedCard(const std::string &filePath);
    // Function to get the bitset representing the punched data for a specific
    // column.
    std::bitset<CARD_ROWS> getColumnData(size_t columnIndex) const;

  private:
    std::array<std::bitset<CARD_ROWS>, CARD_COLUMNS> cardData;
};

#endif // SIM_PUNCHEDCARD_H
