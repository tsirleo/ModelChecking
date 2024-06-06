SOURCE=dpll.cpp
TARGET=test

CFLAGS = -I. -Wall -O3 -std=c++11

all: $(TARGET)

$(TARGET): $(SOURCE)
		g++ $(CFLAGS) -o $@ -I. $^

clean:
		rm -f $(TARGET)
