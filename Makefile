.PHONY: tla sim lint test

# Model check the Phi16 specification with TLC
tla:
	tlc -config Phi16.cfg Phi16.tla

# Replay a trace using the Python simulator
sim:
	python sim_replay.py

# Lint all Python sources with flake8
lint:
	flake8 .

# Run the Python unit tests
test:
	pytest
