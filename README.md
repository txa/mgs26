# Type Theory with Agda — MGS 2026

Course materials for the [Midlands Graduate School 2026](https://www.cs.bham.ac.uk/~mhe/MGS2026/) lecture series on Type Theory with Agda.

**Lecturer:** Thorsten Altenkirch (University of Nottingham)

## Overview

This course introduces dependent type theory through hands-on programming in [Agda](https://wiki.portal.chalmers.se/agda/). We start from the basics and work up to cubical type theory and the univalence axiom.

| Day       | Topic                                                        |
|-----------|--------------------------------------------------------------|
| Monday    | Introduction: natural numbers, equality, induction           |
| Tuesday   | Dependent types in programming: `Vec`, `Fin`, matrices       |
| Wednesday | Dependent types in logic: order relations, natural deduction |
| Thursday  | The mystery of equality: `J`, `K`, extensionality, h-levels |
| Friday    | Cubical type theory: `transp`, `hcomp`, univalence           |

## Prerequisites

Some familiarity with functional programming (Haskell, ML, or similar) is helpful. No prior experience with Agda or type theory is assumed.

## Setup

Install Agda and the standard library:

- [Agda installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
- Recommended editor: VS Code with the [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode) extension, or Emacs with [agda2-mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)

The exercises use Agda's `{! !}` hole syntax — fill in the holes to complete the proofs.

## Exercises

Each day's exercises are in `Exercises/`. They build on material from the lectures, with holes (`{! !}`) marking what you need to prove.
