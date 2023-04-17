.PHONY: fmt

fmt: $(wildcard *.py)
	black *.py

test:
	pytest --doctest-modules --verbose