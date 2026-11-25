module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Palomar Challenge: Two-Window Upper Bounds for Classical `3x + 1` Collatz Infinite Stopping Times

For the shortcut Collatz map `T(n) = n / 2` (`n` even) and `T(n) = (3n + 1) / 2` (`n` odd),
let `N_T(X)` count integers `1 ≤ n ≤ X` whose orbit never drops below `n` (`T^[j] n ≥ n`
for all `j ≥ 1`), and let `shellNeverDrops k` count those in the dyadic shell `[2^k, 2^(k+1))`.

This challenge states:
1. `collatz_two_window_tight_094476_master`: Conditional solely on the quantitative three-place
   Subspace hypothesis `ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R` with
   `H₀ ≤ 2^((49597 / 100000) * 2^40)` (instantiated by Evertse–Ferretti 2013 Theorem 3.1),
   there exist `R` integer band endpoints `K_i ≥ 2^40` such that `shellNeverDrops k ≤ 2^(0.94476 k)`
   outside `[K_i, 3.041 K_i]`, `N_T(X) ≤ 5 X^0.94476` for `X ≥ 2^(2 * 2^40)` outside
   `[2^(K_i), (2^(K_i))^3.06]`, every window `[X₁, X₁^(3.2^(R + 1))]` contains an integer `x`
   with `N_T(x) ≤ 5 x^0.94476`, and `∃ C > 0, ∀ X ≥ 1, N_T(X) ≤ C X^0.94476`.
2. `collatz_two_window_wide_0945_master`: The same four-part bound at exponent `0.945` under
   `ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R`.
3. Unconditional core theorems: `all_shell_neverDrops_le` (`shellNeverDrops k ≤ 2^(0.94995558 k)`
   for every `k ≥ 24`), `two_pow_mul_iterate` (`2^k * T^[k] n = 3^(s_k(n)) * n + B_k(n)`),
   `parityWord_bijective_shell` (2-adic shell parity-word bijection), and
   `suffix_shifted_bernoulli_far_bound` (shifted Bernoulli tree suffix coupling bound).
4. Non-vacuity sanity checks (`neverDrops_one`, `not_neverDrops_three`).
-/

@[expose] public section

namespace CollatzTwoWindowChallenge

/-- Classical Collatz shortcut map: `n / 2` for even `n`, `(3 * n + 1) / 2` for odd `n`. -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Parity bit of `n`: `true` iff `n` is odd. -/
def stepParity (n : ℕ) : Bool :=
  decide (n % 2 = 1)

/-- Length-`k` shortcut parity word of `n`: bit `i` is the parity of `T^[i] n`. -/
def parityWord (k n : ℕ) : Fin k → Bool :=
  fun i => stepParity (T^[i.val] n)

/-- Number of odd inputs among `T^[0] n, ..., T^[k - 1] n`. -/
def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => oddCount k n + if T^[k] n % 2 = 1 then 1 else 0

/-- Integral affine intercept `B_k(n)` in `2^k * T^[k] n = 3^(s_k(n)) * n + B_k(n)`. -/
def affineOffset : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n =>
      if T^[k] n % 2 = 1 then 3 * affineOffset k n + 2 ^ k else affineOffset k n

/-- `n` has infinite stopping time under `T`: `T^[j] n ≥ n` for all `j ≥ 1`. -/
def NeverDrops (n : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → n ≤ T^[j] n

/-- Count of positive integers `1 ≤ n ≤ X` whose shortcut orbit never drops below `n`. -/
noncomputable def N_T (X : ℕ) : ℕ :=
  letI : DecidablePred NeverDrops := Classical.decPred NeverDrops
  ((Finset.Icc 1 X).filter NeverDrops).card

/-- Count of integers in the dyadic shell `[2^k, 2^(k+1))` that never drop below themselves. -/
noncomputable def shellNeverDrops (k : ℕ) : ℕ :=
  letI : DecidablePred NeverDrops := Classical.decPred NeverDrops
  ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter NeverDrops).card

/-- Bernoulli tilted weight `p^(s_k(n)) * (1 - p)^(k - s_k(n))`. -/
def tiltedMass (p : ℝ) (k n : ℕ) : ℝ :=
  p ^ oddCount k n * (1 - p) ^ (k - oddCount k n)

/-- Suffix Bernoulli tilted weight over steps `r, ..., r + L - 1`. -/
def suffixTiltedMass (p : ℝ) (r L n : ℕ) : ℝ :=
  tiltedMass p L (T^[r] n)

/-- Hamming distance between length-`k` parity words of `a` and `b`. -/
def hammingDist : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b =>
      hammingDist k a b + if stepParity (T^[k] a) ≠ stepParity (T^[k] b) then 1 else 0

/-- Suffix Hamming distance between parity words of `a` and `b` on steps `r .. r + L - 1`. -/
def suffixHammingDist (r L a b : ℕ) : ℕ :=
  hammingDist L (T^[r] a) (T^[r] b)

/-- Disagreement coupling contraction factor `λ(p) = 2 * √(p * (1 - p))`. -/
noncomputable def couplingLambda (p : ℝ) : ℝ :=
  2 * Real.sqrt (p * (1 - p))

/-- Normalized `p`-adic absolute value `|x|_p = p^(-v_p(x))` for nonzero `x : ℤ`, and `0` at `0`. -/
noncomputable def padicAbs (p : ℕ) (x : ℤ) : ℝ :=
  if x = 0 then 0 else ((p : ℝ) ^ padicValNat p x.natAbs)⁻¹

/-- The 3-place `{∞, 2, 3}` linear-form product `|X - Z| * |Z| * |X * Z|_2 * |X * Z|_3`. -/
noncomputable def threePlaceProduct (X Z : ℤ) : ℝ :=
  |(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)| * padicAbs 2 (X * Z) * padicAbs 3 (X * Z)

/-- Explicit interface to the quantitative 3-place `{∞, 2, 3}` Subspace Theorem
(never axiomatized). -/
structure ThreePlaceSubspaceHypothesis (δ H₀ : ℝ) (R : ℕ) where
  slopes : Fin R → ℚ
  covers :
    ∀ x z : ℤ, Int.gcd x z = 1 → x ≠ 0 → z ≠ 0 → x ≠ z →
      H₀ ≤ max |(x : ℝ)| |(z : ℝ)| →
      threePlaceProduct x z < ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) ^ (-δ / 2) →
      ∃ i : Fin R, (z : ℚ) / (x : ℚ) = slopes i

/-- Tight-slack `0.94476` four-part master theorem parameterized solely by
`ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R`. -/
theorem collatz_two_window_tight_094476_master {H₀ : ℝ} {R : ℕ}
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hsub : ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R) :
    ∃ leftEnds : Fin R → ℕ,
      (∀ i, 2 ^ 40 ≤ leftEnds i) ∧
      (∀ k : ℕ, 2 ^ 40 ≤ k →
        (∀ i : Fin R, ¬ (leftEnds i ≤ k ∧ (k : ℝ) ≤ (3041 / 1000 : ℝ) * (leftEnds i : ℝ))) →
        (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ ((94476 / 10 ^ 5 : ℝ) * (k : ℝ))) ∧
      (∀ X : ℕ, 2 ^ (2 * 2 ^ 40) ≤ X →
        (∀ i : Fin R, ¬ ((2 : ℝ) ^ (leftEnds i) ≤ (X : ℝ) ∧
          (X : ℝ) ≤ ((2 : ℝ) ^ (leftEnds i)) ^ ((306 : ℝ) / 100))) →
        (N_T X : ℝ) ≤ 5 * (X : ℝ) ^ (94476 / 10 ^ 5 : ℝ)) ∧
      (∀ X₁ : ℝ, ((2 ^ (2 * 2 ^ 40) : ℕ) : ℝ) ≤ X₁ →
        ∃ x : ℕ, X₁ ≤ (x : ℝ) ∧ (x : ℝ) ≤ X₁ ^ (((32 : ℝ) / 10) ^ (R + 1)) ∧
          (N_T x : ℝ) ≤ 5 * (x : ℝ) ^ (94476 / 10 ^ 5 : ℝ)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (N_T X : ℝ) ≤ C * (X : ℝ) ^ (94476 / 10 ^ 5 : ℝ)) := by
  sorry

/-- Wide-slack `0.945` four-part master theorem parameterized solely by
`ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R`. -/
theorem collatz_two_window_wide_0945_master {H₀ : ℝ} {R : ℕ}
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hsub : ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R) :
    ∃ leftEnds : Fin R → ℕ,
      (∀ i, 2 ^ 40 ≤ leftEnds i) ∧
      (∀ k : ℕ, 2 ^ 40 ≤ k →
        (∀ i : Fin R, ¬ (leftEnds i ≤ k ∧ (k : ℝ) ≤ (3041 / 1000 : ℝ) * (leftEnds i : ℝ))) →
        (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ ((945 / 1000 : ℝ) * (k : ℝ))) ∧
      (∀ X : ℕ, 2 ^ (2 * 2 ^ 40) ≤ X →
        (∀ i : Fin R, ¬ ((2 : ℝ) ^ (leftEnds i) ≤ (X : ℝ) ∧
          (X : ℝ) ≤ ((2 : ℝ) ^ (leftEnds i)) ^ ((306 : ℝ) / 100))) →
        (N_T X : ℝ) ≤ 5 * (X : ℝ) ^ (945 / 1000 : ℝ)) ∧
      (∀ X₁ : ℝ, ((2 ^ (2 * 2 ^ 40) : ℕ) : ℝ) ≤ X₁ →
        ∃ x : ℕ, X₁ ≤ (x : ℝ) ∧ (x : ℝ) ≤ X₁ ^ (((32 : ℝ) / 10) ^ (R + 1)) ∧
          (N_T x : ℝ) ≤ 5 * (x : ℝ) ^ (945 / 1000 : ℝ)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (N_T X : ℝ) ≤ C * (X : ℝ) ^ (945 / 1000 : ℝ)) := by
  sorry

/-- Unconditional all-shell bound `shellNeverDrops k ≤ 2^(0.94995558 k)` for every `k ≥ 24`. -/
theorem all_shell_neverDrops_le {k : ℕ} (hk : 24 ≤ k) :
    (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ ((94995558 / 10 ^ 8 : ℝ) * (k : ℝ)) := by
  sorry

/-- Exact `k`-step affine formula: `2^k * T^[k] n = 3^(s_k(n)) * n + B_k(n)`. -/
theorem two_pow_mul_iterate (k n : ℕ) :
    2 ^ k * T^[k] n = 3 ^ oddCount k n * n + affineOffset k n := by
  sorry

/-- Bijection between the dyadic shell `[2^k, 2^(k+1))` and parity words `Fin k → Bool`. -/
theorem parityWord_bijective_shell (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => parityWord k (2 ^ k + r.val)) := by
  sorry

/-- Distant-pair suffix shifted Bernoulli coupling bound `≤ λ(q)^H`. -/
theorem suffix_shifted_bernoulli_far_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r L a d H : ℕ) :
    ∑ u ∈ (Finset.range (2 ^ L)).filter
        (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d)),
      Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
        suffixTiltedMass q r L (a + u * 2 ^ r + d)) ≤
      (couplingLambda q) ^ H := by
  sorry

/-- Non-vacuity check: `1` has infinite stopping time (`T 1 = 2`, `T 2 = 1`). -/
theorem neverDrops_one : NeverDrops 1 := by
  sorry

/-- Non-vacuity check: `3` has finite stopping time (`T^[4] 3 = 2 < 3`). -/
theorem not_neverDrops_three : ¬ NeverDrops 3 := by
  sorry

end CollatzTwoWindowChallenge
