# lean-erm

This repository currently formalizes the deterministic core behind a standard ERM oracle inequality.

The main theorem says: if two real-valued objectives `f` and `fhat` are uniformly within `ε`, and `x` is a `δ`-approximate minimizer of `fhat`, then `x` is a `(2ε + δ)`-approximate minimizer of `f`.

The repository also includes a deterministic threshold-disagreement result:
if a score `s` is uniformly within `ε` of a target score `η`, then the
threshold rules induced by `s` and `η` can disagree only where `η` is within
`ε` of the threshold.

This repository does not yet formalize probability, empirical measures, Hoeffding bounds, VC theory, Rademacher complexity, or finite-class uniform convergence.

## Build

```bash
lake build
lake env lean -T 0 LearningTheory/Discriminator/Threshold.lean
lake env lean -T 0 LearningTheory/ERM/Deterministic.lean
```

Expected result: both commands complete successfully.
