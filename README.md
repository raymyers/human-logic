# Human Logic

> Proof assistant for people who don't know proofs (yet!)

Human Logic is an simple interactive prover supporting First-Order Logic for programmers learning Formal Methods.

Runs on the terminal.
## Usage

Enter propositions in English (or other LLM recognized language). Optionally, use a prefix.
* No prefix = Append to the end as a proposition
* Prefix C = Append to the end conclusion 
* Number prefix = Add/overwrite the numbered line

Statements will be converted to First-Order Logic notation, then into Z3 for verification. 

## Example: First Cause

Input
```
1 Everything that begins to exist has a cause
2 The universe began to exist
C The universe has a cause
```

Output
```
1 ∀ x (BeginsToExist(x) → ∃ y Cause(y, x))
2 BeginsToExist(Universe)
C ∃ y Cause(y, Universe)
```

## Example 2

Input
```
1 All men are mortal
2 Socrates was a man
C Socrates was mortal
```

Output
```
1 ∀ x (Man(x) → Mortal(x))
2 Man(Socrates)
C Mortal(Socrates)
```


## Requirements

* Python 3.10+
* OpenAI access
* Z3 version 3+ (tested on 4.12.4)

## Setup
Set env var OPENAI_API_KEY

To use venv:
```
python -m venv venv
source ./venv/bin/activate
```

Install packages
```
pip install -r requrements.txt
```

## Running

```
python -m human_logic
```

## Checks

```
ruff check --fix .

python -m pytest -v
```
