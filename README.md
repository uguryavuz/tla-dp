# tla-dp

A lightweight workflow for verifying differential privacy (DP) of PlusCal programs in the TLA+ toolchain, via self-products (Barthe et al., 2014).

## What this repo contains
- **`DP.tla`**: Abstract interfaces for DP mechanisms (e.g., `AbsLap`, `AbsExp`) plus reusable definitions/lemmas (e.g., `AbsLapHoareSpec`, `AbsLapAccSpec`) used by proofs and TLC configs.
- **`transform.py`**: Self-product transformation for PlusCal programs (duplicates variables, synchronizes control flow, replaces mechanism calls with `Abs*` invocations), implemented using `tree-sitter-tlaplus`.
- **`2xLaplace/`**: Minimal end-to-end example, including:
  - a transformed spec,
  - a TLAPS proof,
  - a TLC configuration that can also surface too-small privacy budgets as counterexample traces.
- **`SmartSum/`**: Continual-release running-sum case study (2ε-DP). **Under refactoring** in TLA+.
- **`PTR/`**: Propose-Test-Release case study (approximate DP using an accuracy rule for Laplace). **Under refactoring** in TLA+.

## How to use (high level)
1. Write a PlusCal algorithm with mechanism calls written using uninterpreted constants (e.g., `Lap(_)`, `Exp(_,_)`).
2. Run `transform.py` to generate the self-product PlusCal program.
3. Translate the result with the standard PlusCal translator to obtain a TLA+ spec.
4. Use **TLC** to model check invariants (and get counterexample traces for bad budgets) or **TLAPS** to prove invariants.
