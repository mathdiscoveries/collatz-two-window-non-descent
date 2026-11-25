module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

import Mathlib.Tactic

/-!
# Classical Collatz Shortcut Coding, 2-Adic Bijection, and Shifted Parity Coupling

Formalizes the foundational algebraic and 2-adic machinery for the two-window
classical Collatz stopping-time theorem:

1. **Shortcut map and exact `k`-step affine coding (`T`, `oddCount`, `affineOffset`):**
   - `two_pow_mul_iterate`: `2^k * T^[k] n = 3^(oddCount k n) * n + affineOffset k n`.
   - `iterate_add_two_pow_mul`: `T^[k] (n + q * 2^k) = T^[k] n + q * 3^(oddCount k n)`,
     with exact invariance of `parityWord k`, `oddCount k`, and `affineOffset k` modulo `2^k`.
   - `sibling_parity_flip`: translating `n` by `2^k` flips parity bit `k`.
2. **2-adic parity-word bijection (`parityWord_bijective_fin`, `parityWord_bijective_shell`):**
   - The map `r ↦ parityWord k r` is a bijection `Fin (2^k) ≃ (Fin k → Bool)` and
     likewise a bijection from the dyadic shell `[2^k, 2^(k+1))` onto `Fin k → Bool`.
3. **Exact shifted Bernoulli tree coupling (`shifted_bernoulli_tree_identity` & suffix version):**
   - For every depth `k`, every shift `d`, and every tilt `p ∈ (0, 1)`,
     `∑_{r < 2^k} √(μ_p(r) μ_p(r + d)) / λ(p)^{h_k(r, r + d)} = 1`,
     where `λ(p) = 2 √(p (1 - p))`, yielding the exact distant-pair bound `≤ λ(p)^H`.
   - Exact suffix-window version after any fixed prefix length `r`, prefix residue `a`, and shift `d`.
4. **Exact normalized offset, multiplicative trajectory, and constant-weight Hamming balls:**
   - `affineOffset_div_three_pow`, `iterate_div_eq_prod`,
     `affineOffset_le_of_prefix_product_lower`, `prefix_product_lower_of_no_drop`,
     `tiltedMass_sum_eq_one`, and `card_same_weight_hamming_sphere`.
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Shortcut Map, Parity Words, and Affine Recurrences -/

/-- Classical Collatz shortcut map: `n / 2` for even `n`, `(3 * n + 1) / 2` for odd `n`. -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Parity bit of `n`: `true` iff `n` is odd. -/
def stepParity (n : ℕ) : Bool :=
  decide (n % 2 = 1)

/-- Length-`k` shortcut parity word of `n`: bit `i` is the parity of `T^[i] n`. -/
def parityWord (k n : ℕ) : Fin k → Bool :=
  fun i => stepParity (T^[i.val] n)

/-- Number of odd inputs among `T^[0] n, ..., T^[k - 1] n` (denoted `s_k(n)`). -/
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

/-- `n` has finite stopping time under `T`: `T^[j] n < n` for some `j ≥ 1`. -/
def HasFiniteStoppingTime (n : ℕ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ T^[j] n < n

/-- Count of positive integers `1 ≤ n ≤ X` whose shortcut orbit never drops below `n`. -/
noncomputable def N_T (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => NeverDrops n)).card

/-- Count of integers in the dyadic shell `[2^k, 2^(k+1))` that never drop below themselves. -/
noncomputable def shellNeverDrops (k : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => NeverDrops n)).card

theorem neverDrops_iff_not_finiteStoppingTime (n : ℕ) :
    NeverDrops n ↔ ¬ HasFiniteStoppingTime n := by
  simp only [NeverDrops, HasFiniteStoppingTime, not_exists, not_and, not_lt]

theorem T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by
  simp [T, h]

theorem T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  have h2 : n % 2 ≠ 0 := by omega
  simp [T, h2]

theorem two_mul_T_even {n : ℕ} (h : n % 2 = 0) : 2 * T n = n := by
  rw [T_even h]; omega

theorem two_mul_T_odd {n : ℕ} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  rw [T_odd h]; omega

theorem T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  unfold T
  split_ifs with h <;> omega

theorem iterate_T_pos {n : ℕ} (hn : 0 < n) : ∀ k : ℕ, 0 < T^[k] n
  | 0 => hn
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact T_pos (iterate_T_pos hn k)

theorem oddCount_le (k n : ℕ) : oddCount k n ≤ k := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
      simp only [oddCount]
      split_ifs <;> omega

theorem oddCount_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) : oddCount j n ≤ oddCount k n := by
  induction hjk with
  | refl => exact le_rfl
  | @step m _ ih =>
      simp only [oddCount]
      split_ifs <;> omega

theorem oddCount_eq_card_filter (k n : ℕ) :
    oddCount k n = (Finset.univ.filter (fun i : Fin k => parityWord k n i = true)).card := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
      rw [Finset.card_filter, Fin.sum_univ_castSucc]
      simp only [oddCount, ih, Finset.card_filter, parityWord, stepParity,
        Fin.val_castSucc, Fin.val_last, decide_eq_true_eq]

/-- Exact `k`-step affine formula: `2^k * T^[k] n = 3^(s_k(n)) * n + B_k(n)`. -/
theorem two_pow_mul_iterate (k n : ℕ) :
    2 ^ k * T^[k] n = 3 ^ oddCount k n * n + affineOffset k n := by
  induction k with
  | zero => simp [oddCount, affineOffset]
  | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ, mul_assoc]
      by_cases hodd : T^[k] n % 2 = 1
      · have h2T : 2 * T (T^[k] n) = 3 * T^[k] n + 1 := two_mul_T_odd hodd
        rw [h2T, mul_add, mul_one, ← mul_assoc, mul_comm (2 ^ k) 3, mul_assoc, ih]
        simp only [oddCount, affineOffset, hodd, ↓reduceIte, pow_succ]
        ring
      · have heven : T^[k] n % 2 = 0 := by omega
        have h2T : 2 * T (T^[k] n) = T^[k] n := two_mul_T_even heven
        rw [h2T, ih]
        simp only [oddCount, affineOffset, hodd, ↓reduceIte, add_zero]

/-- Prefix-suffix composition for `oddCount`: `s_{r + L}(n) = s_r(n) + s_L(T^[r] n)`. -/
theorem oddCount_add (r L n : ℕ) :
    oddCount (r + L) n = oddCount r n + oddCount L (T^[r] n) := by
  induction L with
  | zero => simp [oddCount]
  | succ L ih =>
      rw [← Nat.add_assoc]
      simp only [oddCount, ih]
      have hcomm : T^[r + L] n = T^[L] (T^[r] n) := by
        rw [Nat.add_comm r L, Function.iterate_add_apply]
      rw [hcomm]
      omega

/-- Exact `2^k`-periodicity of parity words, odd counts, offsets, and affine lift of `T^[k]`. -/
theorem iterate_add_two_pow_mul (k n q : ℕ) :
    T^[k] (n + q * 2 ^ k) = T^[k] n + q * 3 ^ oddCount k n ∧
    oddCount k (n + q * 2 ^ k) = oddCount k n ∧
    affineOffset k (n + q * 2 ^ k) = affineOffset k n ∧
    (∀ i : ℕ, i < k → stepParity (T^[i] (n + q * 2 ^ k)) = stepParity (T^[i] n)) := by
  induction k generalizing q with
  | zero =>
      refine ⟨by simp [oddCount], rfl, rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ k ih =>
      have hrewrite : n + q * 2 ^ (k + 1) = n + (2 * q) * 2 ^ k := by ring
      rw [hrewrite]
      obtain ⟨hT, hs, hB, hpar⟩ := ih (2 * q)
      set m : ℕ := q * 3 ^ oddCount k n
      have h2m : (2 * q) * 3 ^ oddCount k n = 2 * m := by dsimp [m]; ring
      have hmod : T^[k] (n + (2 * q) * 2 ^ k) % 2 = T^[k] n % 2 := by
        rw [hT, h2m]; omega
      have hTsucc :
          T^[k + 1] (n + (2 * q) * 2 ^ k) =
            T^[k + 1] n + q * 3 ^ oddCount (k + 1) n := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hT, h2m]
        simp only [oddCount]
        by_cases hodd : T^[k] n % 2 = 1
        · have hodd' : (T^[k] n + 2 * m) % 2 = 1 := by omega
          rw [T_odd hodd, T_odd hodd']
          simp only [hodd, ↓reduceIte, pow_succ]
          have h3m : q * (3 ^ oddCount k n * 3) = 3 * m := by dsimp [m]; ring
          rw [h3m]
          omega
        · have hev : T^[k] n % 2 = 0 := by omega
          have hev' : (T^[k] n + 2 * m) % 2 = 0 := by omega
          rw [T_even hev, T_even hev']
          simp only [hodd, ↓reduceIte, add_zero]
          change (T^[k] n + 2 * m) / 2 = T^[k] n / 2 + m
          omega
      refine ⟨hTsucc, ?_, ?_, ?_⟩
      · simp only [oddCount, hs, hmod]
      · simp only [affineOffset, hB, hmod]
      · intro i hi
        by_cases hik : i < k
        · exact hpar i hik
        · have hik_eq : i = k := by omega
          subst hik_eq
          simp only [stepParity, hmod]

theorem parityWord_add_two_pow_mul (k n q : ℕ) :
    parityWord k (n + q * 2 ^ k) = parityWord k n := by
  funext i
  exact (iterate_add_two_pow_mul k n q).2.2.2 i.val i.isLt

theorem oddCount_add_two_pow_mul (k n q : ℕ) :
    oddCount k (n + q * 2 ^ k) = oddCount k n :=
  (iterate_add_two_pow_mul k n q).2.1

theorem affineOffset_add_two_pow_mul (k n q : ℕ) :
    affineOffset k (n + q * 2 ^ k) = affineOffset k n :=
  (iterate_add_two_pow_mul k n q).2.2.1

theorem parityWord_mod (k n : ℕ) : parityWord k (n % 2 ^ k) = parityWord k n := by
  have h := parityWord_add_two_pow_mul k (n % 2 ^ k) (n / 2 ^ k)
  have hdiv : n % 2 ^ k + n / 2 ^ k * 2 ^ k = n := by
    rw [mul_comm]; exact Nat.mod_add_div n (2 ^ k)
  rw [hdiv] at h
  exact h.symm

theorem oddCount_mod (k n : ℕ) : oddCount k (n % 2 ^ k) = oddCount k n := by
  have h := oddCount_add_two_pow_mul k (n % 2 ^ k) (n / 2 ^ k)
  have hdiv : n % 2 ^ k + n / 2 ^ k * 2 ^ k = n := by
    rw [mul_comm]; exact Nat.mod_add_div n (2 ^ k)
  rw [hdiv] at h
  exact h.symm

/-- Sibling translation: `n ↦ n + 2^k` shifts `T^[k] n` by the odd integer `3^(s_k(n))`,
flipping parity bit `k`. -/
theorem sibling_iterate (k n : ℕ) :
    T^[k] (n + 2 ^ k) = T^[k] n + 3 ^ oddCount k n := by
  have h := (iterate_add_two_pow_mul k n 1).1
  simpa using h

theorem three_pow_mod_two (s : ℕ) : 3 ^ s % 2 = 1 := by
  induction s with
  | zero => decide
  | succ s ih =>
      rw [pow_succ]
      omega

theorem sibling_parity_flip (k n : ℕ) :
    stepParity (T^[k] (n + 2 ^ k)) = !(stepParity (T^[k] n)) := by
  rw [sibling_iterate]
  have h3 : 3 ^ oddCount k n % 2 = 1 := three_pow_mod_two (oddCount k n)
  have hiff : (T^[k] n + 3 ^ oddCount k n) % 2 = 1 ↔ ¬ (T^[k] n % 2 = 1) := by omega
  simp only [stepParity]
  by_cases h : T^[k] n % 2 = 1
  · have h' : ¬ (T^[k] n + 3 ^ oddCount k n) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (T^[k] n + 3 ^ oddCount k n) % 2 = 1 := by omega
    simp [h, h']

/-! ## 2. Exact 2-Adic Parity-Word Bijection -/

private lemma mod_two_pow_succ_cases (k a : ℕ) :
    a % 2 ^ (k + 1) = a % 2 ^ k ∨ a % 2 ^ (k + 1) = a % 2 ^ k + 2 ^ k := by
  set p := 2 ^ k
  have hp : 0 < p := by positivity
  have h2p : 2 ^ (k + 1) = 2 * p := by dsimp [p]; ring
  rw [h2p]
  set x := a % (2 * p)
  have hlt : x < 2 * p := Nat.mod_lt a (by omega)
  have hmod : x % p = a % p := Nat.mod_mod_of_dvd a ⟨2, by ring⟩
  have hdiv : x / p = 0 ∨ x / p = 1 := by
    have hq : x / p < 2 := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)
    have hq' : x / p ≤ 1 := Nat.lt_succ_iff.mp hq
    exact Nat.le_one_iff_eq_zero_or_eq_one.mp hq'
  have hdm : p * (x / p) + x % p = x := Nat.div_add_mod x p
  rcases hdiv with h0 | h1
  · left; rw [h0] at hdm; omega
  · right; rw [h1] at hdm; omega

/-- Two numbers with the same length-`k` parity word are congruent modulo `2^k`. -/
theorem mod_two_pow_eq_of_parityWord_eq (k : ℕ) :
    ∀ {a b : ℕ}, parityWord k a = parityWord k b → a % 2 ^ k = b % 2 ^ k := by
  induction k with
  | zero => intro a b _; simp [Nat.mod_one]
  | succ k ih =>
      intro a b hab
      have hprefix : parityWord k a = parityWord k b := by
        funext i
        have := congrFun hab i.castSucc
        simpa [parityWord] using this
      have hmodk : a % 2 ^ k = b % 2 ^ k := ih hprefix
      have hlast : stepParity (T^[k] a) = stepParity (T^[k] b) := by
        have := congrFun hab ⟨k, Nat.lt_succ_self k⟩
        simpa [parityWord] using this
      have hlast_a : stepParity (T^[k] (a % 2 ^ (k + 1))) = stepParity (T^[k] a) := by
        have := congrFun (parityWord_mod (k + 1) a) ⟨k, Nat.lt_succ_self k⟩
        simpa [parityWord] using this
      have hlast_b : stepParity (T^[k] (b % 2 ^ (k + 1))) = stepParity (T^[k] b) := by
        have := congrFun (parityWord_mod (k + 1) b) ⟨k, Nat.lt_succ_self k⟩
        simpa [parityWord] using this
      rcases mod_two_pow_succ_cases k a with ha0 | ha1 <;>
        rcases mod_two_pow_succ_cases k b with hb0 | hb1
      · rw [ha0, hb0, hmodk]
      · exfalso
        rw [ha0] at hlast_a
        rw [hb1, ← hmodk, sibling_parity_flip] at hlast_b
        have hcontra : (!stepParity (T^[k] (a % 2 ^ k))) = stepParity (T^[k] (a % 2 ^ k)) :=
          hlast_b.trans (hlast.symm.trans hlast_a.symm)
        cases hval : stepParity (T^[k] (a % 2 ^ k)) <;> rw [hval] at hcontra <;> cases hcontra
      · exfalso
        rw [ha1, sibling_parity_flip] at hlast_a
        rw [hb0, ← hmodk] at hlast_b
        have hcontra : (!stepParity (T^[k] (a % 2 ^ k))) = stepParity (T^[k] (a % 2 ^ k)) :=
          hlast_a.trans (hlast.trans hlast_b.symm)
        cases hval : stepParity (T^[k] (a % 2 ^ k)) <;> rw [hval] at hcontra <;> cases hcontra
      · rw [ha1, hb1, hmodk]

/-- Bijection between residues `Fin (2^k)` and parity words `Fin k → Bool`. -/
theorem parityWord_bijective_fin (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => parityWord k r.val) := by
  have hinj : Function.Injective (fun r : Fin (2 ^ k) => parityWord k r.val) := by
    intro a b hab
    have hmod := mod_two_pow_eq_of_parityWord_eq k hab
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  have hcard : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp [Fintype.card_fin, Fintype.card_bool]
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩

/-- Bijection between the dyadic shell `[2^k, 2^(k+1))` and parity words `Fin k → Bool`. -/
theorem parityWord_bijective_shell (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => parityWord k (2 ^ k + r.val)) := by
  have hEq : (fun r : Fin (2 ^ k) => parityWord k (2 ^ k + r.val)) =
      (fun r : Fin (2 ^ k) => parityWord k r.val) := by
    funext r
    have h := parityWord_add_two_pow_mul k r.val 1
    simpa [Nat.add_comm] using h
  rw [hEq]
  exact parityWord_bijective_fin k

/-! ## 3. Shifted Parity-Tree Coupling (Full Window & Suffix Window) -/

/-- Bernoulli tilted weight `μ_p(k, n) = p^(s_k(n)) * (1 - p)^(k - s_k(n))`. -/
def tiltedMass (p : ℝ) (k n : ℕ) : ℝ :=
  p ^ oddCount k n * (1 - p) ^ (k - oddCount k n)

/-- Suffix odd-step count over steps `r, r + 1, ..., r + L - 1`. -/
def suffixOddCount (r L n : ℕ) : ℕ :=
  oddCount L (T^[r] n)

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

theorem couplingLambda_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < couplingLambda p := by
  unfold couplingLambda
  have : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  positivity

theorem couplingLambda_le_one (p : ℝ) :
    couplingLambda p ≤ 1 := by
  unfold couplingLambda
  have hsq : 4 * (p * (1 - p)) ≤ 1 := by nlinarith [sq_nonneg (2 * p - 1)]
  have : Real.sqrt (4 * (p * (1 - p))) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], Real.sqrt_one] at this
  exact this

theorem tiltedMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k n : ℕ) :
    0 ≤ tiltedMass p k n := by
  unfold tiltedMass
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem tiltedMass_succ (p : ℝ) (k n : ℕ) :
    tiltedMass p (k + 1) n =
      tiltedMass p k n * if T^[k] n % 2 = 1 then p else (1 - p) := by
  unfold tiltedMass
  have hle : oddCount k n ≤ k := oddCount_le k n
  simp only [oddCount]
  by_cases hodd : T^[k] n % 2 = 1
  · simp only [hodd, ↓reduceIte]
    have hsub : k + 1 - (oddCount k n + 1) = k - oddCount k n := by omega
    rw [hsub, pow_succ]
    ring
  · simp only [hodd, ↓reduceIte, add_zero]
    have hsub : k + 1 - oddCount k n = (k - oddCount k n) + 1 := by omega
    rw [hsub, pow_succ]
    ring

theorem tiltedMass_add_two_pow_mul (p : ℝ) (k n q : ℕ) :
    tiltedMass p k (n + q * 2 ^ k) = tiltedMass p k n := by
  simp only [tiltedMass, oddCount_add_two_pow_mul]

theorem hammingDist_add_two_pow_mul (k a b q₁ q₂ : ℕ) :
    hammingDist k (a + q₁ * 2 ^ k) (b + q₂ * 2 ^ k) = hammingDist k a b := by
  induction k generalizing q₁ q₂ with
  | zero => rfl
  | succ k ih =>
      have ha : a + q₁ * 2 ^ (k + 1) = a + (2 * q₁) * 2 ^ k := by ring
      have hb : b + q₂ * 2 ^ (k + 1) = b + (2 * q₂) * 2 ^ k := by ring
      rw [ha, hb]
      simp only [hammingDist]
      have hpa : stepParity (T^[k] (a + (2 * q₁) * 2 ^ k)) = stepParity (T^[k] a) := by
        have hT := (iterate_add_two_pow_mul k a (2 * q₁)).1
        have h2 : (T^[k] a + 2 * (q₁ * 3 ^ oddCount k a)) % 2 = T^[k] a % 2 := by omega
        have heq : 2 * q₁ * 3 ^ oddCount k a = 2 * (q₁ * 3 ^ oddCount k a) := by ring
        simp only [stepParity, hT, heq, h2]
      have hpb : stepParity (T^[k] (b + (2 * q₂) * 2 ^ k)) = stepParity (T^[k] b) := by
        have hT := (iterate_add_two_pow_mul k b (2 * q₂)).1
        have h2 : (T^[k] b + 2 * (q₂ * 3 ^ oddCount k b)) % 2 = T^[k] b % 2 := by omega
        have heq : 2 * q₂ * 3 ^ oddCount k b = 2 * (q₂ * 3 ^ oddCount k b) := by ring
        simp only [stepParity, hT, heq, h2]
      rw [ih (2 * q₁) (2 * q₂), hpa, hpb]

theorem hammingDist_eq_card_filter (k a b : ℕ) :
    hammingDist k a b =
      (Finset.univ.filter (fun i : Fin k => parityWord k a i ≠ parityWord k b i)).card := by
  induction k with
  | zero => simp [hammingDist]
  | succ k ih =>
      rw [Finset.card_filter, Fin.sum_univ_castSucc, hammingDist, ih, Finset.card_filter]
      rfl

/-- Binary-lift coupling invariant: at any node `(x, y)` of depth `k`, the two lifted
children `(x, y)` and `(x + 2^k, y + 2^k)` either both agree or both disagree at bit `k`. -/
theorem shifted_child_agreement_or_flip (k x y : ℕ) :
    (stepParity (T^[k] (x + 2 ^ k)) = stepParity (T^[k] (y + 2 ^ k))) ↔
      (stepParity (T^[k] x) = stepParity (T^[k] y)) := by
  rw [sibling_parity_flip, sibling_parity_flip]
  cases stepParity (T^[k] x) <;> cases stepParity (T^[k] y) <;> decide

/-- Exact binary-lift step for the normalized shifted Bernoulli tree weight. -/
private lemma shifted_step_pair {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (k x y : ℕ) :
    let lam := couplingLambda p
    Real.sqrt (tiltedMass p (k + 1) x * tiltedMass p (k + 1) y) *
        lam⁻¹ ^ hammingDist (k + 1) x y +
      Real.sqrt (tiltedMass p (k + 1) (x + 2 ^ k) * tiltedMass p (k + 1) (y + 2 ^ k)) *
        lam⁻¹ ^ hammingDist (k + 1) (x + 2 ^ k) (y + 2 ^ k) =
      Real.sqrt (tiltedMass p k x * tiltedMass p k y) * lam⁻¹ ^ hammingDist k x y := by
  intro lam
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hmx : 0 ≤ tiltedMass p k x := tiltedMass_nonneg hp0.le hp1.le k x
  have hmy : 0 ≤ tiltedMass p k y := tiltedMass_nonneg hp0.le hp1.le k y
  have hmxy : 0 ≤ tiltedMass p k x * tiltedMass p k y := mul_nonneg hmx hmy
  have hmx' : tiltedMass p k (x + 2 ^ k) = tiltedMass p k x := by
    simpa using tiltedMass_add_two_pow_mul p k x 1
  have hmy' : tiltedMass p k (y + 2 ^ k) = tiltedMass p k y := by
    simpa using tiltedMass_add_two_pow_mul p k y 1
  have hhd' : hammingDist k (x + 2 ^ k) (y + 2 ^ k) = hammingDist k x y := by
    simpa using hammingDist_add_two_pow_mul k x y 1 1
  have hflipx : stepParity (T^[k] (x + 2 ^ k)) = !(stepParity (T^[k] x)) :=
    sibling_parity_flip k x
  have hflipy : stepParity (T^[k] (y + 2 ^ k)) = !(stepParity (T^[k] y)) :=
    sibling_parity_flip k y
  have hmodx : (T^[k] (x + 2 ^ k) % 2 = 1) ↔ ¬ (T^[k] x % 2 = 1) := by
    have := sibling_iterate k x
    have h3 := three_pow_mod_two (oddCount k x)
    rw [this]; omega
  have hmody : (T^[k] (y + 2 ^ k) % 2 = 1) ↔ ¬ (T^[k] y % 2 = 1) := by
    have := sibling_iterate k y
    have h3 := three_pow_mod_two (oddCount k y)
    rw [this]; omega
  have hlam_ne : lam ≠ 0 := (couplingLambda_pos hp0 hp1).ne'
  rw [tiltedMass_succ, tiltedMass_succ, tiltedMass_succ, tiltedMass_succ, hmx', hmy']
  simp only [hammingDist, hhd', hflipx, hflipy]
  by_cases hx : T^[k] x % 2 = 1 <;> by_cases hy : T^[k] y % 2 = 1
  · have hx' : ¬ T^[k] (x + 2 ^ k) % 2 = 1 := hmodx.not.mpr (not_not.mpr hx)
    have hy' : ¬ T^[k] (y + 2 ^ k) % 2 = 1 := hmody.not.mpr (not_not.mpr hy)
    have hpx : stepParity (T^[k] x) = true := by simp [stepParity, hx]
    have hpy : stepParity (T^[k] y) = true := by simp [stepParity, hy]
    simp only [hx, hy, hx', hy', hpx, hpy, ↓reduceIte, ne_eq, not_true_eq_false, add_zero,
      Bool.not_true]
    have h1 : tiltedMass p k x * p * (tiltedMass p k y * p) =
        (tiltedMass p k x * tiltedMass p k y) * (p * p) := by ring
    have h2 : tiltedMass p k x * (1 - p) * (tiltedMass p k y * (1 - p)) =
        (tiltedMass p k x * tiltedMass p k y) * ((1 - p) * (1 - p)) := by ring
    rw [h1, h2, Real.sqrt_mul hmxy, Real.sqrt_mul hmxy,
      Real.sqrt_mul_self hp0.le, Real.sqrt_mul_self h1p.le]
    ring
  · have hx' : ¬ T^[k] (x + 2 ^ k) % 2 = 1 := hmodx.not.mpr (not_not.mpr hx)
    have hy' : T^[k] (y + 2 ^ k) % 2 = 1 := hmody.mpr hy
    have hpx : stepParity (T^[k] x) = true := by simp [stepParity, hx]
    have hpy : stepParity (T^[k] y) = false := by simp [stepParity, hy]
    simp only [hx, hy, hx', hy', hpx, hpy, ↓reduceIte, ne_eq, Bool.true_eq_false,
      not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true]
    have h1 : tiltedMass p k x * p * (tiltedMass p k y * (1 - p)) =
        (tiltedMass p k x * tiltedMass p k y) * (p * (1 - p)) := by ring
    have h2 : tiltedMass p k x * (1 - p) * (tiltedMass p k y * p) =
        (tiltedMass p k x * tiltedMass p k y) * (p * (1 - p)) := by ring
    rw [h1, h2, Real.sqrt_mul hmxy, pow_succ]
    have hcancel : 2 * Real.sqrt (p * (1 - p)) * lam⁻¹ = 1 := by
      change lam * lam⁻¹ = 1
      exact mul_inv_cancel₀ hlam_ne
    calc
      Real.sqrt (tiltedMass p k x * tiltedMass p k y) * Real.sqrt (p * (1 - p)) *
          (lam⁻¹ ^ hammingDist k x y * lam⁻¹) +
        Real.sqrt (tiltedMass p k x * tiltedMass p k y) * Real.sqrt (p * (1 - p)) *
          (lam⁻¹ ^ hammingDist k x y * lam⁻¹)
          = Real.sqrt (tiltedMass p k x * tiltedMass p k y) * lam⁻¹ ^ hammingDist k x y *
              (2 * Real.sqrt (p * (1 - p)) * lam⁻¹) := by ring
      _ = Real.sqrt (tiltedMass p k x * tiltedMass p k y) * lam⁻¹ ^ hammingDist k x y := by
          rw [hcancel, mul_one]
  · have hx' : T^[k] (x + 2 ^ k) % 2 = 1 := hmodx.mpr hx
    have hy' : ¬ T^[k] (y + 2 ^ k) % 2 = 1 := hmody.not.mpr (not_not.mpr hy)
    have hpx : stepParity (T^[k] x) = false := by simp [stepParity, hx]
    have hpy : stepParity (T^[k] y) = true := by simp [stepParity, hy]
    simp only [hx, hy, hx', hy', hpx, hpy, ↓reduceIte, ne_eq, Bool.false_eq_true,
      not_false_eq_true, Bool.not_false, Bool.not_true, Bool.true_eq_false]
    have h1 : tiltedMass p k x * (1 - p) * (tiltedMass p k y * p) =
        (tiltedMass p k x * tiltedMass p k y) * (p * (1 - p)) := by ring
    have h2 : tiltedMass p k x * p * (tiltedMass p k y * (1 - p)) =
        (tiltedMass p k x * tiltedMass p k y) * (p * (1 - p)) := by ring
    rw [h1, h2, Real.sqrt_mul hmxy, pow_succ]
    have hcancel : 2 * Real.sqrt (p * (1 - p)) * lam⁻¹ = 1 := by
      change lam * lam⁻¹ = 1
      exact mul_inv_cancel₀ hlam_ne
    calc
      Real.sqrt (tiltedMass p k x * tiltedMass p k y) * Real.sqrt (p * (1 - p)) *
          (lam⁻¹ ^ hammingDist k x y * lam⁻¹) +
        Real.sqrt (tiltedMass p k x * tiltedMass p k y) * Real.sqrt (p * (1 - p)) *
          (lam⁻¹ ^ hammingDist k x y * lam⁻¹)
          = Real.sqrt (tiltedMass p k x * tiltedMass p k y) * lam⁻¹ ^ hammingDist k x y *
              (2 * Real.sqrt (p * (1 - p)) * lam⁻¹) := by ring
      _ = Real.sqrt (tiltedMass p k x * tiltedMass p k y) * lam⁻¹ ^ hammingDist k x y := by
          rw [hcancel, mul_one]
  · have hx' : T^[k] (x + 2 ^ k) % 2 = 1 := hmodx.mpr hx
    have hy' : T^[k] (y + 2 ^ k) % 2 = 1 := hmody.mpr hy
    have hpx : stepParity (T^[k] x) = false := by simp [stepParity, hx]
    have hpy : stepParity (T^[k] y) = false := by simp [stepParity, hy]
    simp only [hx, hy, hx', hy', hpx, hpy, ↓reduceIte, ne_eq, not_true_eq_false, add_zero,
      Bool.not_false]
    have h1 : tiltedMass p k x * (1 - p) * (tiltedMass p k y * (1 - p)) =
        (tiltedMass p k x * tiltedMass p k y) * ((1 - p) * (1 - p)) := by ring
    have h2 : tiltedMass p k x * p * (tiltedMass p k y * p) =
        (tiltedMass p k x * tiltedMass p k y) * (p * p) := by ring
    rw [h1, h2, Real.sqrt_mul hmxy, Real.sqrt_mul hmxy,
      Real.sqrt_mul_self hp0.le, Real.sqrt_mul_self h1p.le]
    ring

/-- Helper: splitting a sum over `range (2^(k+1))` into `r` and `r + 2^k` for `r ∈ range (2^k)`. -/
private lemma sum_range_two_pow_succ {α : Type*} [AddCommMonoid α] (k : ℕ) (f : ℕ → α) :
    ∑ r ∈ Finset.range (2 ^ (k + 1)), f r =
      ∑ r ∈ Finset.range (2 ^ k), (f r + f (r + 2 ^ k)) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  rw [hpow, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Nat.add_comm]

/-- **Exact Shifted Bernoulli Tree Identity (Full Window):**
For every depth `k`, every shift `d`, and every tilt `p ∈ (0, 1)`,
`∑_{r=0}^{2^k - 1} √(μ_p(k, r) μ_p(k, r + d)) * λ(p)^{-h_k(r, r + d)} = 1`. -/
theorem shifted_bernoulli_tree_identity {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k d : ℕ) :
    ∑ r ∈ Finset.range (2 ^ k),
      Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
        (couplingLambda p)⁻¹ ^ hammingDist k r (r + d) = 1 := by
  induction k with
  | zero =>
      simp [tiltedMass, oddCount, hammingDist]
  | succ k ih =>
      rw [sum_range_two_pow_succ]
      have hterm :
          ∀ r ∈ Finset.range (2 ^ k),
            Real.sqrt (tiltedMass p (k + 1) r * tiltedMass p (k + 1) (r + d)) *
                (couplingLambda p)⁻¹ ^ hammingDist (k + 1) r (r + d) +
              Real.sqrt (tiltedMass p (k + 1) (r + 2 ^ k) *
                  tiltedMass p (k + 1) (r + 2 ^ k + d)) *
                (couplingLambda p)⁻¹ ^ hammingDist (k + 1) (r + 2 ^ k) (r + 2 ^ k + d) =
              Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
                (couplingLambda p)⁻¹ ^ hammingDist k r (r + d) := by
        intro r _
        have hcomm : r + 2 ^ k + d = (r + d) + 2 ^ k := by omega
        rw [hcomm]
        exact shifted_step_pair hp0 hp1 k r (r + d)
      rw [Finset.sum_congr rfl hterm]
      exact ih

/-- **Distant-Pair Shifted Bernoulli Bound (Full Window):**
The sum of geometric-mean tilted weights over all `r < 2^k` at Hamming distance `≥ H`
from `r + d` is at most `λ(p)^H`. -/
theorem shifted_bernoulli_far_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k d H : ℕ) :
    ∑ r ∈ (Finset.range (2 ^ k)).filter (fun r => H ≤ hammingDist k r (r + d)),
      Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) ≤
      (couplingLambda p) ^ H := by
  have hlam_pos : 0 < couplingLambda p := couplingLambda_pos hp0 hp1
  have hlam_le : couplingLambda p ≤ 1 := couplingLambda_le_one p
  have hpow_pos : 0 < (couplingLambda p) ^ H := pow_pos hlam_pos H
  have hsum_le :
      ∑ r ∈ (Finset.range (2 ^ k)).filter (fun r => H ≤ hammingDist k r (r + d)),
        Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
          (couplingLambda p)⁻¹ ^ H ≤
      ∑ r ∈ Finset.range (2 ^ k),
        Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
          (couplingLambda p)⁻¹ ^ hammingDist k r (r + d) := by
    calc
      ∑ r ∈ (Finset.range (2 ^ k)).filter (fun r => H ≤ hammingDist k r (r + d)),
          Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
            (couplingLambda p)⁻¹ ^ H
        ≤ ∑ r ∈ (Finset.range (2 ^ k)).filter (fun r => H ≤ hammingDist k r (r + d)),
            Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
              (couplingLambda p)⁻¹ ^ hammingDist k r (r + d) := by
          apply Finset.sum_le_sum
          intro r hr
          have hH : H ≤ hammingDist k r (r + d) := (Finset.mem_filter.mp hr).2
          have hinv_ge : 1 ≤ (couplingLambda p)⁻¹ := (one_le_inv₀ hlam_pos).mpr hlam_le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv_ge hH) (Real.sqrt_nonneg _)
      _ ≤ ∑ r ∈ Finset.range (2 ^ k),
            Real.sqrt (tiltedMass p k r * tiltedMass p k (r + d)) *
              (couplingLambda p)⁻¹ ^ hammingDist k r (r + d) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro r _ _
          exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (inv_nonneg.mpr hlam_pos.le) _)
  rw [shifted_bernoulli_tree_identity hp0 hp1 k d, ← Finset.sum_mul] at hsum_le
  have hmul := mul_le_mul_of_nonneg_right hsum_le hpow_pos.le
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hlam_pos.ne', one_pow, mul_one, one_mul] at hmul
  exact hmul

/-- **Exact Suffix Shifted Bernoulli Tree Identity:**
Fixing prefix length `r`, prefix residue `a`, and shift `d`, lifting the high bits
`u ∈ [0, 2^L)` of `n = a + u * 2^r` and `n' = n + d` yields an exact normalized
suffix tree weight of `1` for any suffix tilt `q ∈ (0, 1)`. -/
theorem suffix_shifted_bernoulli_tree_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r L a d : ℕ) :
    ∑ u ∈ Finset.range (2 ^ L),
      Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
          suffixTiltedMass q r L (a + u * 2 ^ r + d)) *
        (couplingLambda q)⁻¹ ^ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d) = 1 := by
  induction L with
  | zero =>
      simp [suffixTiltedMass, tiltedMass, oddCount, suffixHammingDist, hammingDist]
  | succ L ih =>
      rw [sum_range_two_pow_succ]
      have hterm :
          ∀ u ∈ Finset.range (2 ^ L),
            Real.sqrt (suffixTiltedMass q r (L + 1) (a + u * 2 ^ r) *
                suffixTiltedMass q r (L + 1) (a + u * 2 ^ r + d)) *
              (couplingLambda q)⁻¹ ^
                suffixHammingDist r (L + 1) (a + u * 2 ^ r) (a + u * 2 ^ r + d) +
            Real.sqrt (suffixTiltedMass q r (L + 1) (a + (u + 2 ^ L) * 2 ^ r) *
                suffixTiltedMass q r (L + 1) (a + (u + 2 ^ L) * 2 ^ r + d)) *
              (couplingLambda q)⁻¹ ^
                suffixHammingDist r (L + 1) (a + (u + 2 ^ L) * 2 ^ r)
                  (a + (u + 2 ^ L) * 2 ^ r + d) =
            Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
                suffixTiltedMass q r L (a + u * 2 ^ r + d)) *
              (couplingLambda q)⁻¹ ^
                suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d) := by
        intro u _
        set x := a + u * 2 ^ r
        set y := a + u * 2 ^ r + d
        have hxL : a + (u + 2 ^ L) * 2 ^ r = x + 2 ^ L * 2 ^ r := by
          dsimp [x]; ring
        have hyL : x + 2 ^ L * 2 ^ r + d = y + 2 ^ L * 2 ^ r := by
          dsimp [x, y]; ring
        rw [hxL, hyL]
        have hTx : T^[r] (x + 2 ^ L * 2 ^ r) = T^[r] x + 3 ^ oddCount r x * 2 ^ L := by
          have := (iterate_add_two_pow_mul r x (2 ^ L)).1
          rw [this]; ring
        have hTy : T^[r] (y + 2 ^ L * 2 ^ r) = T^[r] y + 3 ^ oddCount r y * 2 ^ L := by
          have := (iterate_add_two_pow_mul r y (2 ^ L)).1
          rw [this]; ring
        set sx := 3 ^ oddCount r x
        set sy := 3 ^ oddCount r y
        have hsx_odd : sx % 2 = 1 := three_pow_mod_two (oddCount r x)
        have hsy_odd : sy % 2 = 1 := three_pow_mod_two (oddCount r y)
        have hsx_eq : sx * 2 ^ L = 2 ^ L + (sx / 2) * 2 ^ (L + 1) := by
          have h2 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
          rw [h2]; have : sx = 1 + 2 * (sx / 2) := by omega
          calc sx * 2 ^ L = (1 + 2 * (sx / 2)) * 2 ^ L := by rw [← this]
            _ = 2 ^ L + (sx / 2) * (2 * 2 ^ L) := by ring
        have hsy_eq : sy * 2 ^ L = 2 ^ L + (sy / 2) * 2 ^ (L + 1) := by
          have h2 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
          rw [h2]; have : sy = 1 + 2 * (sy / 2) := by omega
          calc sy * 2 ^ L = (1 + 2 * (sy / 2)) * 2 ^ L := by rw [← this]
            _ = 2 ^ L + (sy / 2) * (2 * 2 ^ L) := by ring
        have hmx_red :
            suffixTiltedMass q r (L + 1) (x + 2 ^ L * 2 ^ r) =
              tiltedMass q (L + 1) (T^[r] x + 2 ^ L) := by
          unfold suffixTiltedMass
          rw [hTx, hsx_eq, ← Nat.add_assoc]
          exact tiltedMass_add_two_pow_mul q (L + 1) (T^[r] x + 2 ^ L) (sx / 2)
        have hmy_red :
            suffixTiltedMass q r (L + 1) (y + 2 ^ L * 2 ^ r) =
              tiltedMass q (L + 1) (T^[r] y + 2 ^ L) := by
          unfold suffixTiltedMass
          rw [hTy, hsy_eq, ← Nat.add_assoc]
          exact tiltedMass_add_two_pow_mul q (L + 1) (T^[r] y + 2 ^ L) (sy / 2)
        have hhd_red :
            suffixHammingDist r (L + 1) (x + 2 ^ L * 2 ^ r) (y + 2 ^ L * 2 ^ r) =
              hammingDist (L + 1) (T^[r] x + 2 ^ L) (T^[r] y + 2 ^ L) := by
          unfold suffixHammingDist
          rw [hTx, hTy, hsx_eq, hsy_eq, ← Nat.add_assoc, ← Nat.add_assoc]
          exact hammingDist_add_two_pow_mul (L + 1) (T^[r] x + 2 ^ L) (T^[r] y + 2 ^ L)
            (sx / 2) (sy / 2)
        rw [hmx_red, hmy_red, hhd_red]
        unfold suffixTiltedMass suffixHammingDist
        exact shifted_step_pair hq0 hq1 L (T^[r] x) (T^[r] y)
      rw [Finset.sum_congr rfl hterm]
      exact ih

/-- **Distant-Pair Suffix Shifted Bernoulli Bound:**
For fixed prefix length `r`, residue `a`, and shift `d`, the sum of geometric-mean
suffix tilted weights over high-bit lifts `u < 2^L` at suffix Hamming distance `≥ H`
is at most `λ(q)^H`. -/
theorem suffix_shifted_bernoulli_far_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r L a d H : ℕ) :
    ∑ u ∈ (Finset.range (2 ^ L)).filter
        (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d)),
      Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
        suffixTiltedMass q r L (a + u * 2 ^ r + d)) ≤
      (couplingLambda q) ^ H := by
  have hlam_pos : 0 < couplingLambda q := couplingLambda_pos hq0 hq1
  have hlam_le : couplingLambda q ≤ 1 := couplingLambda_le_one q
  have hpow_pos : 0 < (couplingLambda q) ^ H := pow_pos hlam_pos H
  have hsum_le :
      ∑ u ∈ (Finset.range (2 ^ L)).filter
          (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d)),
        Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
          suffixTiltedMass q r L (a + u * 2 ^ r + d)) * (couplingLambda q)⁻¹ ^ H ≤
      ∑ u ∈ Finset.range (2 ^ L),
        Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
          suffixTiltedMass q r L (a + u * 2 ^ r + d)) *
          (couplingLambda q)⁻¹ ^ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d) := by
    calc
      _ ≤ ∑ u ∈ (Finset.range (2 ^ L)).filter
            (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d)),
          Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
            suffixTiltedMass q r L (a + u * 2 ^ r + d)) *
            (couplingLambda q)⁻¹ ^ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d) := by
        apply Finset.sum_le_sum
        intro u hu
        have hH : H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + d) :=
          (Finset.mem_filter.mp hu).2
        have hinv_ge : 1 ≤ (couplingLambda q)⁻¹ := (one_le_inv₀ hlam_pos).mpr hlam_le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv_ge hH) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u _ _
        exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (inv_nonneg.mpr hlam_pos.le) _)
  rw [suffix_shifted_bernoulli_tree_identity hq0 hq1 r L a d, ← Finset.sum_mul] at hsum_le
  have hmul := mul_le_mul_of_nonneg_right hsum_le hpow_pos.le
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hlam_pos.ne', one_pow, mul_one, one_mul] at hmul
  exact hmul

/-- Total tilted mass over all residues modulo `2^k` equals `1`. -/
theorem tiltedMass_sum_eq_one (p : ℝ) (k : ℕ) :
    ∑ r ∈ Finset.range (2 ^ k), tiltedMass p k r = 1 := by
  induction k with
  | zero => simp [tiltedMass, oddCount]
  | succ k ih =>
      rw [sum_range_two_pow_succ]
      have hterm :
          ∀ r ∈ Finset.range (2 ^ k),
            tiltedMass p (k + 1) r + tiltedMass p (k + 1) (r + 2 ^ k) = tiltedMass p k r := by
        intro r _
        have hmr : tiltedMass p k (r + 2 ^ k) = tiltedMass p k r := by
          simpa using tiltedMass_add_two_pow_mul p k r 1
        have hmod : (T^[k] (r + 2 ^ k) % 2 = 1) ↔ ¬ (T^[k] r % 2 = 1) := by
          have := sibling_iterate k r
          have h3 := three_pow_mod_two (oddCount k r)
          rw [this]; omega
        rw [tiltedMass_succ, tiltedMass_succ, hmr]
        by_cases hr : T^[k] r % 2 = 1
        · have hr' : ¬ T^[k] (r + 2 ^ k) % 2 = 1 := hmod.not.mpr (not_not.mpr hr)
          simp only [hr, hr', ↓reduceIte]; ring
        · have hr' : T^[k] (r + 2 ^ k) % 2 = 1 := hmod.mpr hr
          simp only [hr, hr', ↓reduceIte]; ring
      rw [Finset.sum_congr rfl hterm]
      exact ih

/-- Tilted-mass cardinality bound: any set of residues modulo `2^k` whose elements each
have tilted mass at least `M > 0` has cardinality at most `1 / M`. -/
theorem card_le_inv_of_tiltedMass_ge {p M : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (k : ℕ) (A : Finset ℕ) (hAsub : A ⊆ Finset.range (2 ^ k))
    (hAmin : ∀ r ∈ A, M ≤ tiltedMass p k r) :
    (A.card : ℝ) ≤ M⁻¹ := by
  have h1 : (A.card : ℝ) * M ≤ ∑ r ∈ A, tiltedMass p k r := by
    calc (A.card : ℝ) * M = ∑ _r ∈ A, M := by simp
      _ ≤ ∑ r ∈ A, tiltedMass p k r := Finset.sum_le_sum hAmin
  have h2 : ∑ r ∈ A, tiltedMass p k r ≤ ∑ r ∈ Finset.range (2 ^ k), tiltedMass p k r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hAsub
    intro r _ _
    exact tiltedMass_nonneg hp0 hp1 k r
  rw [tiltedMass_sum_eq_one] at h2
  have h3 : (A.card : ℝ) * M ≤ 1 := h1.trans h2
  rw [← one_div]
  exact (le_div_iff₀ hM).mpr h3

/-! ## 4. Normalized Affine Offset, Multiplicative Formula, and No-Drop Prefix Bound -/

/-- Exact rational/real expansion of the normalized offset `B_k(n) / 3^(s_k(n))`. -/
theorem affineOffset_div_three_pow (k n : ℕ) :
    (affineOffset k n : ℝ) / (3 : ℝ) ^ oddCount k n =
      ∑ j ∈ Finset.range k,
        if T^[j] n % 2 = 1 then (2 : ℝ) ^ j / (3 : ℝ) ^ (oddCount j n + 1) else 0 := by
  induction k with
  | zero => simp [affineOffset, oddCount]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [affineOffset, oddCount]
      by_cases hodd : T^[k] n % 2 = 1
      · simp only [hodd, ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        rw [add_div, pow_succ (3 : ℝ), mul_comm ((3 : ℝ) ^ oddCount k n) 3,
          mul_div_mul_left _ _ (by norm_num : (3 : ℝ) ≠ 0), ih,
          mul_comm 3 ((3 : ℝ) ^ oddCount k n), ← pow_succ]
      · simp only [hodd, ↓reduceIte, add_zero]
        exact ih

/-- Exact multiplicative trajectory identity:
`T^[k] n / n = (3^(s_k(n)) / 2^k) * ∏_{j < k, odd} (1 + 1 / (3 * T^[j] n))`. -/
theorem iterate_div_eq_prod {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (T^[k] n : ℝ) / (n : ℝ) =
      ((3 : ℝ) ^ oddCount k n / (2 : ℝ) ^ k) *
        ∏ j ∈ Finset.range k,
          if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else 1 := by
  induction k with
  | zero =>
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp [oddCount, div_self hn']
  | succ k ih =>
      rw [Finset.prod_range_succ, Function.iterate_succ_apply']
      have hxk_pos : 0 < (T^[k] n : ℝ) := Nat.cast_pos.mpr (iterate_T_pos hn k)
      have hxk_ne : (T^[k] n : ℝ) ≠ 0 := hxk_pos.ne'
      simp only [oddCount]
      by_cases hodd : T^[k] n % 2 = 1
      · simp only [hodd, ↓reduceIte]
        have hstep : (T (T^[k] n) : ℝ) = (3 * (T^[k] n : ℝ) + 1) / 2 := by
          have h2 := two_mul_T_odd hodd
          have h2r : (2 : ℝ) * (T (T^[k] n) : ℝ) = 3 * (T^[k] n : ℝ) + 1 := by exact_mod_cast h2
          linarith
        have hfac : (3 * (T^[k] n : ℝ) + 1) / 2 =
            (3 / 2) * (T^[k] n : ℝ) * (1 + 1 / (3 * (T^[k] n : ℝ))) := by
          field_simp [hxk_ne]
        rw [hstep, hfac]
        calc
          (3 / 2 * (T^[k] n : ℝ) * (1 + 1 / (3 * (T^[k] n : ℝ)))) / (n : ℝ)
            = (3 / 2) * ((T^[k] n : ℝ) / (n : ℝ)) * (1 + 1 / (3 * (T^[k] n : ℝ))) := by ring
          _ = (3 / 2) * (((3 : ℝ) ^ oddCount k n / (2 : ℝ) ^ k) *
                ∏ j ∈ Finset.range k,
                  if T^[j] n % 2 = 1 then 1 + 1 / (3 * (T^[j] n : ℝ)) else 1) *
                (1 + 1 / (3 * (T^[k] n : ℝ))) := by rw [ih]
          _ = ((3 : ℝ) ^ (oddCount k n + 1) / (2 : ℝ) ^ (k + 1)) *
                ((∏ j ∈ Finset.range k,
                  if T^[j] n % 2 = 1 then 1 + 1 / (3 * (T^[j] n : ℝ)) else 1) *
                (1 + 1 / (3 * (T^[k] n : ℝ)))) := by
              rw [pow_succ, pow_succ]; ring
      · simp only [hodd, ↓reduceIte, add_zero, mul_one]
        have hev : T^[k] n % 2 = 0 := by omega
        have hstep : (T (T^[k] n) : ℝ) = (T^[k] n : ℝ) / 2 := by
          have h2 := two_mul_T_even hev
          have h2r : (2 : ℝ) * (T (T^[k] n) : ℝ) = (T^[k] n : ℝ) := by exact_mod_cast h2
          linarith
        rw [hstep]
        calc
          ((T^[k] n : ℝ) / 2) / (n : ℝ) = (1 / 2) * ((T^[k] n : ℝ) / (n : ℝ)) := by ring
          _ = (1 / 2) * (((3 : ℝ) ^ oddCount k n / (2 : ℝ) ^ k) *
                ∏ j ∈ Finset.range k,
                  if T^[j] n % 2 = 1 then 1 + 1 / (3 * (T^[j] n : ℝ)) else 1) := by rw [ih]
          _ = ((3 : ℝ) ^ oddCount k n / (2 : ℝ) ^ (k + 1)) *
                ∏ j ∈ Finset.range k,
                  if T^[j] n % 2 = 1 then 1 + 1 / (3 * (T^[j] n : ℝ)) else 1 := by
              rw [pow_succ]; ring

/-- If every prefix `1 ≤ i ≤ k` satisfies `2^((1 - e) * i) ≤ 3^(s_i(n))` with `e ≥ 0`,
then the normalized affine offset satisfies `B_k(n) / 3^(s_k(n)) ≤ (k / 2) * 2^(e * k)`. -/
theorem affineOffset_le_of_prefix_product_lower {e : ℝ} (he : 0 ≤ e) (k n : ℕ)
    (hpref : ∀ i : ℕ, 1 ≤ i → i ≤ k →
      (2 : ℝ) ^ ((1 - e) * (i : ℝ)) ≤ (3 : ℝ) ^ oddCount i n) :
    (affineOffset k n : ℝ) / (3 : ℝ) ^ oddCount k n ≤
      ((k : ℝ) / 2) * (2 : ℝ) ^ (e * (k : ℝ)) := by
  rw [affineOffset_div_three_pow]
  have hterm : ∀ j ∈ Finset.range k,
      (if T^[j] n % 2 = 1 then (2 : ℝ) ^ j / (3 : ℝ) ^ (oddCount j n + 1) else 0) ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (e * (k : ℝ)) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    split_ifs with hodd
    · have hs : oddCount (j + 1) n = oddCount j n + 1 := by simp [oddCount, hodd]
      have hp := hpref (j + 1) (by omega) (by omega)
      rw [hs] at hp
      have h2pos : 0 < (2 : ℝ) ^ ((1 - e) * ((j + 1 : ℕ) : ℝ)) := by positivity
      have hdiv : (2 : ℝ) ^ j / (3 : ℝ) ^ (oddCount j n + 1) ≤
          (2 : ℝ) ^ j / (2 : ℝ) ^ ((1 - e) * ((j + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) h2pos hp
      have hpow_eq : (2 : ℝ) ^ j / (2 : ℝ) ^ ((1 - e) * ((j + 1 : ℕ) : ℝ)) =
          (1 / 2 : ℝ) * (2 : ℝ) ^ (e * ((j + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        have hexp : (j : ℝ) - (1 - e) * ((j + 1 : ℕ) : ℝ) = -1 + e * ((j + 1 : ℕ) : ℝ) := by
          push_cast; ring
        rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
        ring
      rw [hpow_eq] at hdiv
      have hmono : (2 : ℝ) ^ (e * ((j + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (e * (k : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        have hjk' : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ k)
        exact mul_le_mul_of_nonneg_left hjk' he
      linarith
    · positivity
  calc
    ∑ j ∈ Finset.range k,
        (if T^[j] n % 2 = 1 then (2 : ℝ) ^ j / (3 : ℝ) ^ (oddCount j n + 1) else 0)
      ≤ ∑ _j ∈ Finset.range k, ((1 / 2 : ℝ) * (2 : ℝ) ^ (e * (k : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = ((k : ℝ) / 2) * (2 : ℝ) ^ (e * (k : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- If `n` never drops below `n` through step `k` and `1 + 1 / (3 * n) ≤ 2^e`, then
every prefix `0 ≤ i ≤ k` satisfies `2^((1 - e) * i) ≤ 3^(s_i(n))`. -/
theorem prefix_product_lower_of_no_drop {e : ℝ} {n k : ℕ} (hn : 0 < n)
    (hstep : 1 + 1 / (3 * (n : ℝ)) ≤ (2 : ℝ) ^ e)
    (hnodrop : ∀ j : ℕ, j ≤ k → n ≤ T^[j] n) :
    ∀ i : ℕ, i ≤ k → (2 : ℝ) ^ ((1 - e) * (i : ℝ)) ≤ (3 : ℝ) ^ oddCount i n := by
  intro i hi
  have h1 : (1 : ℝ) ≤ (T^[i] n : ℝ) / (n : ℝ) := by
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [one_le_div hn']
    exact_mod_cast hnodrop i hi
  rw [iterate_div_eq_prod hn i] at h1
  have hprod_le :
      (∏ j ∈ Finset.range i,
        if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else 1) ≤
        ((2 : ℝ) ^ e) ^ i := by
    have hstep_j : ∀ j : ℕ, j < i →
        0 ≤ (if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else (1 : ℝ)) ∧
        (if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else (1 : ℝ)) ≤ (2 : ℝ) ^ e := by
      intro j hji
      split_ifs
      · have hxj : 0 < (T^[j] n : ℝ) := Nat.cast_pos.mpr (iterate_T_pos hn j)
        have hge : (n : ℝ) ≤ (T^[j] n : ℝ) := by exact_mod_cast hnodrop j (by omega)
        have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
        have hdiv : 1 / (3 * (T^[j] n : ℝ)) ≤ 1 / (3 * (n : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        exact ⟨by positivity, by linarith⟩
      · have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
        exact ⟨by norm_num, by linarith [show (0 : ℝ) < 1 / (3 * (n : ℝ)) by positivity]⟩
    suffices ∀ m : ℕ, m ≤ i →
        (∏ j ∈ Finset.range m,
          if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else 1) ≤ ((2 : ℝ) ^ e) ^ m from
      this i le_rfl
    intro m hm
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [Finset.prod_range_succ, pow_succ]
        have hprev := ihm (by omega)
        have hcur := hstep_j m (by omega)
        have hprev_nonneg : 0 ≤ ∏ j ∈ Finset.range m,
            (if T^[j] n % 2 = 1 then (1 + 1 / (3 * (T^[j] n : ℝ))) else (1 : ℝ)) :=
          Finset.prod_nonneg fun j hj => (hstep_j j (by have := Finset.mem_range.mp hj; omega)).1
        exact mul_le_mul hprev hcur.2 hcur.1 (by positivity)
  have h2 : (1 : ℝ) ≤ ((3 : ℝ) ^ oddCount i n / (2 : ℝ) ^ i) * ((2 : ℝ) ^ e) ^ i :=
    h1.trans (mul_le_mul_of_nonneg_left hprod_le (by positivity))
  have h2pow_pos : 0 < (2 : ℝ) ^ i := by positivity
  have hmul : (2 : ℝ) ^ i ≤ (3 : ℝ) ^ oddCount i n * ((2 : ℝ) ^ e) ^ i := by
    have := mul_le_mul_of_nonneg_right h2 h2pow_pos.le
    rw [one_mul] at this
    have hrhs : (3 : ℝ) ^ oddCount i n / (2 : ℝ) ^ i * ((2 : ℝ) ^ e) ^ i * (2 : ℝ) ^ i =
        (3 : ℝ) ^ oddCount i n * ((2 : ℝ) ^ e) ^ i := by
      field_simp [h2pow_pos.ne']
    rwa [hrhs] at this
  have hdiv : (2 : ℝ) ^ i / ((2 : ℝ) ^ e) ^ i ≤ (3 : ℝ) ^ oddCount i n := by
    rw [div_le_iff₀ (by positivity)]
    exact hmul
  have hlhs : (2 : ℝ) ^ ((1 - e) * (i : ℝ)) = (2 : ℝ) ^ i / ((2 : ℝ) ^ e) ^ i := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ e) i, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  rwa [hlhs]

/-- Concrete threshold `n ≥ 2^24` gives `1 + 1 / (3 * n) ≤ 2^(10^{-7})`. -/
theorem step_correction_le_two_pow_1e7 {n : ℕ} (hn : 2 ^ 24 ≤ n) :
    1 + 1 / (3 * (n : ℝ)) ≤ (2 : ℝ) ^ ((1 : ℝ) / 10 ^ 7) := by
  have hn_ge : (2 ^ 24 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 : ℝ) / 5 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have harg : 1 / (3 * (n : ℝ)) ≤ ((1 : ℝ) / 10 ^ 7) * Real.log 2 := by
    have h1 : 1 / (3 * (n : ℝ)) ≤ 1 / (3 * (2 ^ 24 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have h2 : 1 / (3 * (2 ^ 24 : ℝ)) ≤ ((1 : ℝ) / 10 ^ 7) * (1 / 5) := by norm_num
    have h3 : ((1 : ℝ) / 10 ^ 7) * (1 / 5) ≤ ((1 : ℝ) / 10 ^ 7) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    exact h1.trans (h2.trans h3)
  calc
    1 + 1 / (3 * (n : ℝ)) ≤ Real.exp (1 / (3 * (n : ℝ))) := by
      linarith [Real.add_one_le_exp (1 / (3 * (n : ℝ)))]
    _ ≤ Real.exp (((1 : ℝ) / 10 ^ 7) * Real.log 2) := Real.exp_le_exp.mpr harg
    _ = (2 : ℝ) ^ ((1 : ℝ) / 10 ^ 7) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]

/-! ## 5. Constant-Weight Hamming Ball Identity (Close-Pair Counting) -/

/-- Number of `true` entries in a Boolean word `w : Fin L → Bool`. -/
def wordWeight {L : ℕ} (w : Fin L → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => w i = true)).card

/-- Hamming distance between two Boolean words `u, v : Fin L → Bool`. -/
def wordHamming {L : ℕ} (u v : Fin L → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => u i ≠ v i)).card

/-- For two length-`L` Boolean words with the SAME Hamming weight, the number of `1 → 0`
switches equals the number of `0 → 1` switches, so their Hamming distance is even. -/
theorem same_weight_switches_eq {L : ℕ} (u v : Fin L → Bool)
    (hwt : wordWeight u = wordWeight v) :
    (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card =
      (Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)).card := by
  have hu : wordWeight u =
      (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = true)).card +
      (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card := by
    unfold wordWeight
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp; cases v i <;> simp
    · rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; rw [h1.2] at h2; cases h2.2
  have hv : wordWeight v =
      (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = true)).card +
      (Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)).card := by
    unfold wordWeight
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp; cases u i <;> simp
    · rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; rw [h1.1] at h2; cases h2.1
  omega

theorem wordHamming_same_weight_eq_two_mul {L : ℕ} (u v : Fin L → Bool)
    (hwt : wordWeight u = wordWeight v) :
    wordHamming u v =
      2 * (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card := by
  have hsw := same_weight_switches_eq u v hwt
  have hpart : wordHamming u v =
      (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card +
      (Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)).card := by
    unfold wordHamming
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp; cases u i <;> cases v i <;> simp
    · rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; rw [h1.1] at h2; cases h2.1
  omega

/-- Exact constant-weight Hamming sphere count: given `u : Fin L → Bool` of weight `j`,
the number of words `v : Fin L → Bool` of weight `j` at Hamming distance `2 * d` from `u`
equals `Nat.choose j d * Nat.choose (L - j) d`. -/
theorem card_same_weight_hamming_sphere {L : ℕ} (u : Fin L → Bool) (d : ℕ) :
    (Finset.univ.filter (fun v : Fin L → Bool =>
      wordWeight v = wordWeight u ∧ wordHamming u v = 2 * d)).card =
      Nat.choose (wordWeight u) d * Nat.choose (L - wordWeight u) d := by
  set S1 : Finset (Fin L) := Finset.univ.filter (fun i : Fin L => u i = true)
  set S0 : Finset (Fin L) := Finset.univ.filter (fun i : Fin L => u i = false)
  have hS1_card : S1.card = wordWeight u := rfl
  have hS0_card : S0.card = L - wordWeight u := by
    have hunion : S1 ∪ S0 = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S1, S0]
      cases u i <;> simp
    have hdisj : Disjoint S1 S0 := by
      rw [Finset.disjoint_left]; intro i h1 h2; simp [S1, S0] at h1 h2; rw [h1] at h2; cases h2
    have hsum : S1.card + S0.card = L := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hS0_card, ← hS1_card, ← Finset.card_powersetCard, ← Finset.card_powersetCard,
    ← Finset.card_product]
  apply Finset.card_bij
    (fun (v : Fin L → Bool) _ =>
      (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false),
       Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)))
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hwt, hdist⟩ := hv.2
    have hsw := same_weight_switches_eq u v hwt.symm
    have h2d := wordHamming_same_weight_eq_two_mul u v hwt.symm
    have hc1 : (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card = d := by
      omega
    have hc0 : (Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)).card = d := by
      omega
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨?_, hc1⟩, ⟨?_, hc0⟩⟩
    · intro i hi; simp [S1] at hi ⊢; exact hi.1
    · intro i hi; simp [S0] at hi ⊢; exact hi.1
  · intro v₁ hv₁ v₂ hv₂ hpair
    have h1 : Finset.univ.filter (fun i : Fin L => u i = true ∧ v₁ i = false) =
        Finset.univ.filter (fun i : Fin L => u i = true ∧ v₂ i = false) :=
      congrArg Prod.fst hpair
    have h2 : Finset.univ.filter (fun i : Fin L => u i = false ∧ v₁ i = true) =
        Finset.univ.filter (fun i : Fin L => u i = false ∧ v₂ i = true) :=
      congrArg Prod.snd hpair
    funext i
    cases hui : u i
    · have hi : (i ∈ Finset.univ.filter (fun j : Fin L => u j = false ∧ v₁ j = true)) ↔
          (i ∈ Finset.univ.filter (fun j : Fin L => u j = false ∧ v₂ j = true)) := by
        rw [h2]
      simp [hui] at hi
      cases hv1 : v₁ i <;> cases hv2 : v₂ i <;> simp [hv1, hv2] at hi ⊢
    · have hi : (i ∈ Finset.univ.filter (fun j : Fin L => u j = true ∧ v₁ j = false)) ↔
          (i ∈ Finset.univ.filter (fun j : Fin L => u j = true ∧ v₂ j = false)) := by
        rw [h1]
      simp [hui] at hi
      cases hv1 : v₁ i <;> cases hv2 : v₂ i <;> simp [hv1, hv2] at hi ⊢
  · intro p hp
    rcases p with ⟨A, B⟩
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hAsub, hAcard⟩, ⟨hBsub, hBcard⟩⟩ := hp
    let v : Fin L → Bool := fun i =>
      if u i = true then decide (i ∉ A) else decide (i ∈ B)
    have hAeq : Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false) = A := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, v]
      constructor
      · intro ⟨hui, hvi⟩
        simp only [hui, ↓reduceIte, decide_eq_false_iff_not, not_not] at hvi
        exact hvi
      · intro hi
        have hui : u i = true := by
          have := hAsub hi; simp [S1] at this; exact this
        simp [hui, hi]
    have hBeq : Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true) = B := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, v]
      constructor
      · intro ⟨hui, hvi⟩
        simp only [hui, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hvi
        exact hvi
      · intro hi
        have hui : u i = false := by
          have := hBsub hi; simp [S0] at this; exact this
        simp [hui, hi]
    have hwt_v : wordWeight v = wordWeight u := by
      have h1 : wordWeight u =
          (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = true)).card +
          (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = false)).card := by
        unfold wordWeight
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext i; simp; cases v i <;> simp
        · rw [Finset.disjoint_left]; intro i x1 x2; simp at x1 x2; rw [x1.2] at x2; cases x2.2
      have h2 : wordWeight v =
          (Finset.univ.filter (fun i : Fin L => u i = true ∧ v i = true)).card +
          (Finset.univ.filter (fun i : Fin L => u i = false ∧ v i = true)).card := by
        unfold wordWeight
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext i; simp; cases u i <;> simp
        · rw [Finset.disjoint_left]; intro i x1 x2; simp at x1 x2; rw [x1.1] at x2; cases x2.1
      rw [hAeq, hAcard] at h1; rw [hBeq, hBcard] at h2
      omega
    have hdist_v : wordHamming u v = 2 * d := by
      rw [wordHamming_same_weight_eq_two_mul u v hwt_v.symm, hAeq, hAcard]
    refine ⟨v, ?_, Prod.ext hAeq hBeq⟩
    simp [hwt_v, hdist_v, hS1_card]

end CollatzTwoWindow
