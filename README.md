# tla-dp

Verifying differential privacy of PlusCal programs in TLA⁺, by adapting
the self-product construction of Barthe et al. (CSF 2014).

## Contents

- **`DP.tla`** — Reusable module declaring `AbsLap`/`AbsExp` and their
  Hoare and accuracy specifications. Each mechanism takes its per-call
  privacy parameter ε as the first argument.
- **`transform.py`** — Self-product transformation for PlusCal source. 
  Built using 
  [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus),
  (and assumes the Python bindings are installed).
- **`examples/`** — Case studies. Each subdirectory symlinks `DP.tla`
  from the repository root.
  - **`2xLaplace/`** — Two sequential Laplace calls. (2ε)-DP, with TLAPS
    proof and a TLC model checking setup for refuting too-tight budgets.
  - **`smartsum/`** — SmartSum (Chan et al., 2011). Continual-release
    noisy prefix sums, (2ε)-DP. Complete with TLAPS proof and TLC model
    checking setup.
  - **`ptr/`** — Propose-Test-Release (Dwork & Lei, 2009). Approximate
    DP, with both standard and accuracy specs of Laplace used in the
    same proof. Includes a `DTI.tla` module for distance-to-instability.
    Currently only TLAPS proof available.

## Conventions

Privacy parameters (`Epsilon`) are `CONSTANT`s declared
in each algorithm's own module, not globally in `DP.tla`. 
Each mechanism call passes ε explicitly.

## Usage

1. Write a PlusCal algorithm. Declare `Epsilon` as a `CONSTANT`. Use
   `Lap(Epsilon, e)` and `Exp(Epsilon, s, e)` for mechanism calls.
2. Run `python transform.py <algorithm>.tla` to produce the self-product
   `<algorithm>_transf.tla`.
3. Run the standard PlusCal translator on the result.
4. Extend the translated module to either prove the DP invariant in
   TLAPS or model-check it in TLC with `Epsilon` instantiated to a unit
   value (1), and the values domain instantiated to a bounded range of
   integers.

## Reference

Barthe, Gaboardi, Gallego Arias, Hsu, Kunz, Strub. *Proving Differential
Privacy in Hoare Logic.* CSF 2014.
