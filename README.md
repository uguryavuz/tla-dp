# tla-dp

Differential privacy verification in TLA+, via self-products (Barthe et al., 2014).

## What this repo contains
- **`DP.tla`**: Abstract interfaces for DP mechanisms (e.g., `AbsLap`, `AbsExp`) plus reusable definitions/lemmas (e.g., `AbsLapHoareSpec`, `AbsLapAccSpec`).
- **`transform.py`**: Self-product transformation for PlusCal programs (duplicates variables, synchronizes control flow, replaces mechanism calls with `Abs*` invocations), implemented using [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus)
- **`2xLaplace/`**: Minimal example, including:
  - original program,
  - transformed spec,
  - TLAPS proof,
  - model-checking module and TLC configuration to test too-small privacy budgets as counterexample traces.
- **`SmartSum/`**: Continual-release running-sum case study. **Under refactoring** 🛠️ 
- **`PTR/`**: Propose-Test-Release case study (approximate DP using an accuracy rule for Laplace). **Under refactoring** 🛠️ 

## How to use
1. Write a PlusCal algorithm with mechanism calls written using uninterpreted constants (e.g., `Lap(_)`, `Exp(_,_)`).
2. Run `transform.py` on the .tla file containing the algorithm to generate the self-product PlusCal program.
3. Translate the result with the standard PlusCal translator (e.g. by parsing file) to obtain a TLA+ spec.
4. Extend the module - to use TLC to model check invariants (and get counterexample traces for bad budgets) or TLAPS to prove invariants.
