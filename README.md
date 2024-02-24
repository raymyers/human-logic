# FOL Assistant

FOL (First-Order Logic) Assistant is an simple interactive prover for developers learning Formal Methods.

Runs on the terminal.

## Example 1
1 Everything that begins to exist has a cause
2 The universe began to exist
C The universe has a cause

## Example 2
1 All men are mortal
2 Socrates was a man
C Socrates was mortal

## Requirements

* Python 3
* Z3 for prover support

## Running

```
pip install -r requrements.txt

python main.py
``

## Checks

```
ruff check --fix .
```