SRC=my_malloc.c printing.c
GCC=gcc -std=gnu11 -lm

.PHONY: compile_and_push
compile_and_push:
	@#	Compile the source file(s). If successful, push the changes
	@$(GCC) -c $(SRC) && \
	(git add $(SRC); \
	git commit -m "Latest build"; \
	git push; \
	echo "Successfully recorded changes")

.PHONY: submit_part1
submit_part1:
	@git tag -fa v1.0 -m "Part 1"
	@git push -f --tags
	@echo "Part 1 submission complete"

.PHONY: submit_final
submit_final:
	@git tag -fa v2.0 -m "Final"
	@git push -f --tags
	@echo "Final submission complete"

.PHONY: clean
clean:
	rm -f *.o
