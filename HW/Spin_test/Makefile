all: counterexample

checker: three_pots.pml
	spin -a three_pots.pml
	gcc -o pan.o pan.c
	./pan.o

counterexample: checker
	spin -t three_pots.pml

clean:
	rm -f pan.* three_pots.pml.trail *.tmp
