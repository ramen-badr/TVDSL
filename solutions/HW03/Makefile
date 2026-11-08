CFLAGS = -std=gnu99 -O2 -Wall -Wextra -I../HW01

../HW01/dfa.h: ../HW01/hw01
	cd ../HW01 && ./hw01 > /dev/null

../HW01/hw01: ../HW01/hw01.c
	$(MAKE) -C ../HW01 hw01

hw03: hw03.c ../HW01/dfa.h
	$(CC) $(CFLAGS) -o hw03 hw03.c

test: hw03
	./hw03 ../../project/examples/*/*.funny

.PHONY: test
