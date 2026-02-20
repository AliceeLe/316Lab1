# Lab 1 (C0-Arrays) — Python Starter

This starter code provides:
- A parser for the Lab 1 C0-Arrays subset (`src/parse.py`, `src/c0.py`)
- A Z3 encoding + helpers for discharging VCs (`src/solver.py`)

You implement the analyzer (WLP/VC generation) in `src/wlp.py`.

Notes:
- The parser normalizes programs by hoisting potentially-unsafe expression
  subterms (division/modulo and array reads) into fresh temporary assignments.
- The language disallows array aliasing: `int[]` variables cannot be assigned
  except via `alloc_array` or indexed writes.

## Setup

Install dependencies:
```bash
pip install -r requirements.txt
```

## Build

```bash
make
```

This produces `c0_vc`.

## Run

```bash
./c0_vc example.c0
```

Exit codes: `0` valid, `2` unsafe, `1` error.
