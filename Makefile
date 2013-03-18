BIN=Example

all: clean run cleanObj

$(BIN): % : %.hs
	ghc  $< -o $(BIN)

PHONY: run
run: $(BIN)
	./$(BIN)

clean:
	rm -rf $(BIN) *.hi *.o

cleanObj:
	rm -rf *.hi *.o
