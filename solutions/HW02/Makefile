CFLAGS = -std=gnu99 -O2 -Wall -Wextra -I../HW01

../HW01/dfa.h: ../HW01/hw01
	cd ../HW01 && ./hw01 > /dev/null

../HW01/hw01: ../HW01/hw01.c
	$(MAKE) -C ../HW01 hw01

hw02: hw02.c ../HW01/dfa.h
	$(CC) $(CFLAGS) -o hw02 hw02.c

test: hw02
	./hw02 ../../project/examples/*/*.funny

.PHONY: test
