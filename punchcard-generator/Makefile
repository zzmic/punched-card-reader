CC = gcc
CFLAGS = -std=gnu11 -Wall -Wextra -Wpedantic -O2
LDFLAGS = -lm

TARGET = pcgen

all: $(TARGET)

$(TARGET): pcgen.c
	$(CC) $(CFLAGS) -o $(TARGET) pcgen.c $(LDFLAGS)

clean:
	rm -f $(TARGET)

.PHONY: all clean rebuild
