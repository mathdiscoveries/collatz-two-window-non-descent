# Classical $3x+1$ Collatz Infinite Stopping Times: Two-Window Upper Bound $N_T(X) = O(X^{0.94476})$

Lean 4 (`v4.35.0` + Mathlib `v4.35.0`) formalization of the two-window ineffective upper bounds $N_T(X) = O(X^{0.94476})$ and $N_T(X) = O(X^{0.945})$ for the count $N_T(X)$ of integers $1 \le n \le X$ with infinite stopping time under the classical shortcut Collatz map $T(n) = n/2$ ($n$ even), $(3n+1)/2$ ($n$ odd).

- **Author / Director:** Tyler B. Hughes (generated and checked by AI research agents built and directed by Tyler B. Hughes)
- **Review status:** Unrefereed. No human mathematician has yet refereed the proof.
- **Companion page & working draft:** https://mathdiscoveries.org/results/collatz-two-window-non-descent

## What is formally verified

- `CollatzTwoWindowChallenge.collatz_two_window_tight_094476_master`: Four-part bound at exponent `0.94476` (via a 401-leaf `decide +kernel` BSP cover), parameterized explicitly by `ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R` and `H₀ ≤ 2^((49597 / 100000) * 2^40)`.
- `CollatzTwoWindowChallenge.collatz_two_window_wide_0945_master`: Four-part bound at exponent `0.945` (via a 202-leaf `decide +kernel` BSP cover), parameterized explicitly by `ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R`.
- `CollatzTwoWindowChallenge.all_shell_neverDrops_le`: Unconditional all-shell bound `shellNeverDrops k ≤ 2^(0.94995558 k)` for every `k ≥ 24`.
- `CollatzTwoWindowChallenge.two_pow_mul_iterate`, `parityWord_bijective_shell`, and `suffix_shifted_bernoulli_far_bound`: Unconditional shortcut affine trajectory, 2-adic shell parity bijection, and shifted Bernoulli tree suffix coupling bound.
- `CollatzTwoWindowChallenge.neverDrops_one` and `not_neverDrops_three`: Non-vacuity sanity checks.

All proofs compile with zero `sorry`, zero `native_decide`, zero custom axioms, and depend solely on Lean's three standard axioms `{propext, Classical.choice, Quot.sound}`. The quantitative three-place Subspace Theorem (Schlickewei 1990; Evertse–Ferretti 2013 Theorem 3.1) is passed explicitly as a `structure` parameter and is not axiomatized or proved inside Lean.

## Build & verify

```sh
lake build
lake env lean CollatzTwoWindow/Verify.lean
lake comparator --inadvisably-no-sandbox --config comparator.json
```
