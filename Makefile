all: example.txt

example.txt: *.hs
	runghc -W Main.hs > example.txt

clean:
	-rm -f *.hi *.o
