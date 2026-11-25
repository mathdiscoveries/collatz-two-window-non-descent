module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pure-Kernel Rational and Real-Logarithm Certificates for Paper 1

Verifies every numerical constant, logarithm enclosure, separation threshold,
Evertse–Ferretti line-count bound, `0.0516` fixed-height margin, high-product tail,
all-shell Lagarias bound, and prefactor absorption inequality in the Lean 4 kernel
with ZERO `sorry` and ZERO `native_decide`:

1. **Positive-term `atanh` logarithm enclosure (`real_log_atanh_bounds`, `atanh5_real_bounds`):**
   - Pure calculus proof (Mean Value Theorem on `[0, z]`) and closed-form pure-`Nat`
     5-term evaluators (`atanh5LowerNum`, `atanh5Den`, `atanh5UpperNum`, `atanh5UpperDen`)
     with cleared-denominator soundness lemmas (`atanh5_log_gt_of_nat`, `atanh5_log_lt_of_nat`,
     `neg_logb2_ge_of_nat`, `neg_logb2_le_of_nat`).
2. **Exact enclosures for `log_3 2` and Lagarias (1985) binary entropy `H_2(log_3 2)`:**
   - `log3_two_bounds`: `63092975 / 10^8 < Real.log 2 / Real.log 3 < 63092976 / 10^8`.
   - `lagarias_entropy_bounds`: `0.949955 < H_2(log_3 2) < 0.949956`.
   - `all_shell_lagarias_tilt_bound`: `B(1, p_-(1 - 10^{-7}); 0.63093) < 0.94995558`.
   - `high_product_tail_bound`: `B(1, 1.012 * p_-; 0.64) < 0.943928`.
3. **Shorter-window `0.0516` fixed-height margin (`shorter_window_00516_margin`,
   `shorter_window_00516_real_constants`).**
4. **Separation-band thresholds and ratios (`separation_bands_tight_cert`, `separation_bands_wide_cert`).**
5. **Evertse–Ferretti (2013) rational & real line-count bounds:**
   - `evertse_ferretti_line_count_tight`: `< 10^58` at `Q = 20,000,000`, `k_* = 2^28`.
   - `evertse_ferretti_line_count_wide`: `< 10^43` at `Q = 20,000`, `k_* = 2^20`.
6. **Prefactor absorption (`k ≥ 2^40`) & cumulative band slack:**
   - `prefactor_absorption_ge_two_pow_40`: `65 + 3 * log_2(k + 1) < 4 * 10^{-9} * k`.
   - `cumulative_band_slack_and_lagarias_gain`.
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Positive-Term `atanh` Calculus Enclosure for `Real.log` -/

/-- Partial sum `2 * ∑_{m=0}^{N-1} z^(2m+1) / (2m+1)` in `ℝ`. -/
noncomputable def atanhPartial (N : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ m ∈ Finset.range N, z ^ (2 * m + 1) / (2 * m + 1 : ℝ)

/-- Upper remainder bound `2 * z^(2N+1) / ((2N+1) * (1 - z^2))` in `ℝ`. -/
noncomputable def atanhTail (N : ℕ) (z : ℝ) : ℝ :=
  2 * z ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - z ^ 2))

/-- Binary cross-entropy cost `B(a, j; z) = -j * log_2(z) - (a - j) * log_2(1 - z)` in `ℝ`. -/
noncomputable def crossEntropy (a j z : ℝ) : ℝ :=
  j * (-Real.logb 2 z) + (a - j) * (-Real.logb 2 (1 - z))

/-- Binary entropy `H_2(p) = -p * log_2(p) - (1 - p) * log_2(1 - p)` in `ℝ`. -/
noncomputable def binEntropy (p : ℝ) : ℝ :=
  crossEntropy 1 p p

private lemma hasDerivAt_atanhPartial (N : ℕ) (t : ℝ) :
    HasDerivAt (atanhPartial N) (2 * ∑ m ∈ Finset.range N, t ^ (2 * m)) t := by
  unfold atanhPartial
  apply HasDerivAt.const_mul
  have hsum :
      HasDerivAt (fun x : ℝ => ∑ m ∈ Finset.range N, x ^ (2 * m + 1) / (2 * m + 1 : ℝ))
        (∑ m ∈ Finset.range N, t ^ (2 * m)) t := by
    apply HasDerivAt.fun_sum
    intro m _
    have hpow : HasDerivAt (fun x : ℝ => x ^ (2 * m + 1))
        (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m)) t := by
      simpa using hasDerivAt_pow (2 * m + 1) t
    have hdiv := hpow.div_const (2 * m + 1 : ℝ)
    have hne : (2 * m + 1 : ℝ) ≠ 0 := by positivity
    have hsimp : (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m)) / (2 * m + 1 : ℝ) = t ^ (2 * m) := by
      push_cast; field_simp [hne]
    rwa [hsimp] at hdiv
  exact hsum

private lemma hasDerivAt_log_ratio {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt (fun x : ℝ => Real.log (1 + x) - Real.log (1 - x)) (2 / (1 - t ^ 2)) t := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t :=
    h1.log (by linarith)
  have hlog2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - t)) t :=
    h2.log (by linarith)
  have hsub := hlog1.sub hlog2
  have hne1 : 1 + t ≠ 0 := by linarith
  have hne2 : 1 - t ≠ 0 := by linarith
  have hne3 : 1 - t ^ 2 ≠ 0 := by
    have hmul : (1 - t) * (1 + t) = 1 - t ^ 2 := by ring
    rw [← hmul]; exact mul_ne_zero hne2 hne1
  have halg : 1 / (1 + t) - -1 / (1 - t) = 2 / (1 - t ^ 2) := by
    field_simp [hne1, hne2, hne3]; ring
  rwa [halg] at hsub

private lemma atanh_deriv_diff (N : ℕ) {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt (fun x : ℝ => Real.log (1 + x) - Real.log (1 - x) - atanhPartial N x)
      (2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
  have h := (hasDerivAt_log_ratio ht1 ht2).sub (hasDerivAt_atanhPartial N t)
  have h1t2_pos : 0 < 1 - t ^ 2 := by
    have hmul : 0 < (1 - t) * (1 + t) := mul_pos (by linarith) (by linarith)
    linarith [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
  have hne : 1 - t ^ 2 ≠ 0 := h1t2_pos.ne'
  have hne' : t ^ 2 - 1 ≠ 0 := by linarith
  have ht2_ne : t ^ 2 ≠ 1 := by intro heq; apply hne'; linarith
  have hgeom : ∑ m ∈ Finset.range N, t ^ (2 * m) = (1 - t ^ (2 * N)) / (1 - t ^ 2) := by
    have hpow : ∀ m : ℕ, t ^ (2 * m) = (t ^ 2) ^ m := fun m => by rw [← pow_mul]
    simp_rw [hpow]
    rw [geom_sum_eq ht2_ne, ← pow_mul]
    field_simp [hne, hne']; ring
  rw [hgeom] at h
  have halg : 2 / (1 - t ^ 2) - 2 * ((1 - t ^ (2 * N)) / (1 - t ^ 2)) =
      2 * t ^ (2 * N) / (1 - t ^ 2) := by
    field_simp [hne]; ring
  rwa [halg] at h

/-- **Exact Positive-Term `atanh` Calculus Enclosure for `Real.log`:**
For every `v ≥ 1` and `N : ℕ`, setting `z = (v - 1) / (v + 1) ∈ [0, 1)`,
`atanhPartial N z ≤ Real.log v ≤ atanhPartial N z + atanhTail N z`. -/
theorem real_log_atanh_bounds (N : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    atanhPartial N ((v - 1) / (v + 1)) ≤ Real.log v ∧
    Real.log v ≤ atanhPartial N ((v - 1) / (v + 1)) + atanhTail N ((v - 1) / (v + 1)) := by
  set z := (v - 1) / (v + 1)
  have hvpos : 0 < v + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hvpos.le
  have hz1 : z < 1 := (div_lt_one hvpos).mpr (by linarith)
  have hlogv : Real.log v = Real.log (1 + z) - Real.log (1 - z) := by
    have h1 : 1 + z = 2 * v / (v + 1) := by dsimp [z]; field_simp [hvpos.ne']; ring
    have h2 : 1 - z = 2 / (v + 1) := by dsimp [z]; field_simp [hvpos.ne']; ring
    have hv_eq : v = (1 + z) / (1 - z) := by
      rw [h1, h2]; field_simp [hvpos.ne']
    conv_lhs => rw [hv_eq]
    exact Real.log_div (by linarith) (by linarith)
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - atanhPartial N t
  have hf0 : f 0 = 0 := by simp [f, atanhPartial]
  have hf_deriv : ∀ t ∈ Set.Icc (0 : ℝ) z,
      HasDerivAt f (2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
    intro t ⟨ht0, htz⟩
    exact atanh_deriv_diff N (by linarith) (lt_of_le_of_lt htz hz1)
  have hf_mono : MonotoneOn f (Set.Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
    · exact fun t ht => (hf_deriv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hf_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hmem : t ∈ Set.Icc (0 : ℝ) z := interior_subset ht
      rw [(hf_deriv t hmem).deriv]
      have ht1 : t < 1 := lt_of_le_of_lt hmem.2 hz1
      have hden : 0 < 1 - t ^ 2 := by
        have hmul : 0 < (1 - t) * (1 + t) := mul_pos (by linarith) (by linarith [hmem.1])
        linarith [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
      exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hmem.1 _)) hden.le
  have hlo : atanhPartial N z ≤ Real.log v := by
    have := hf_mono (Set.left_mem_Icc.mpr hz0) (Set.right_mem_Icc.mpr hz0) hz0
    rw [hf0] at this
    dsimp [f] at this
    linarith [hlogv]
  let g : ℝ → ℝ := fun t =>
    2 * t ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - z ^ 2)) - f t
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have h1z2 : 0 < 1 - z ^ 2 := by
    have hmul : 0 < (1 - z) * (1 + z) := mul_pos (by linarith) (by linarith)
    linarith [show (1 - z) * (1 + z) = 1 - z ^ 2 by ring]
  have hg_deriv : ∀ t ∈ Set.Icc (0 : ℝ) z,
      HasDerivAt g (2 * t ^ (2 * N) / (1 - z ^ 2) - 2 * t ^ (2 * N) / (1 - t ^ 2)) t := by
    intro t ht
    have hpow : HasDerivAt (fun x : ℝ => x ^ (2 * N + 1))
        (((2 * N + 1 : ℕ) : ℝ) * t ^ (2 * N)) t := by
      simpa using hasDerivAt_pow (2 * N + 1) t
    have hfirst :
        HasDerivAt (fun x : ℝ => 2 * x ^ (2 * N + 1) / ((2 * N + 1 : ℝ) * (1 - z ^ 2)))
          (2 * t ^ (2 * N) / (1 - z ^ 2)) t := by
      have h1 := (hpow.const_mul 2).div_const ((2 * N + 1 : ℝ) * (1 - z ^ 2))
      have hne : (2 * N + 1 : ℝ) ≠ 0 := by positivity
      have halg : 2 * (((2 * N + 1 : ℕ) : ℝ) * t ^ (2 * N)) / ((2 * N + 1 : ℝ) * (1 - z ^ 2)) =
          2 * t ^ (2 * N) / (1 - z ^ 2) := by
        push_cast; field_simp [hne, h1z2.ne']
      rwa [halg] at h1
    exact hfirst.sub (hf_deriv t ht)
  have hg_mono : MonotoneOn g (Set.Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
    · exact fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hmem : t ∈ Set.Icc (0 : ℝ) z := interior_subset ht
      rw [(hg_deriv t hmem).deriv]
      have hden_le : 1 - z ^ 2 ≤ 1 - t ^ 2 := by
        have hmul : 0 ≤ (z - t) * (z + t) := mul_nonneg (by linarith [hmem.2]) (by linarith [hmem.1])
        linarith [show (1 - t ^ 2) - (1 - z ^ 2) = (z - t) * (z + t) by ring]
      have hdiv : 2 * t ^ (2 * N) / (1 - t ^ 2) ≤ 2 * t ^ (2 * N) / (1 - z ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg hmem.1 _)) h1z2 hden_le
      linarith
  have hhi : Real.log v ≤ atanhPartial N z + atanhTail N z := by
    have := hg_mono (Set.left_mem_Icc.mpr hz0) (Set.right_mem_Icc.mpr hz0) hz0
    rw [hg0] at this
    dsimp [g, f, atanhTail] at this ⊢
    linarith [hlogv]
  exact ⟨hlo, hhi⟩

/-- Closed-form 5-term `atanh` expansion over `ℕ` for `v = a / b ≥ 1`, with `u = a - b`, `w = a + b`:
exact numerator over `315 * w^9` (since `lcm(1,3,5,7,9) = 315`). Zero `Rat`/GCD overhead. -/
def atanh5LowerNum (u w : ℕ) : ℕ :=
  2 * (315 * u * w ^ 8 + 105 * u ^ 3 * w ^ 6 + 63 * u ^ 5 * w ^ 4 +
    45 * u ^ 7 * w ^ 2 + 35 * u ^ 9)

def atanh5Den (w : ℕ) : ℕ :=
  315 * w ^ 9

/-- Exact integer numerator for the 5-term upper bound `atanhPartial 5 + atanhTail 5`
over common denominator `3465 * w^9 * (w^2 - u^2)`. -/
def atanh5UpperNum (u w : ℕ) : ℕ :=
  11 * (w * w - u * u) * atanh5LowerNum u w + 630 * u ^ 11

def atanh5UpperDen (u w : ℕ) : ℕ :=
  3465 * w ^ 9 * (w * w - u * u)

theorem atanh5_real_bounds {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    (atanh5LowerNum (a - b) (a + b) : ℝ) / (atanh5Den (a + b) : ℝ) ≤
      Real.log ((a : ℝ) / (b : ℝ)) ∧
    Real.log ((a : ℝ) / (b : ℝ)) ≤
      (atanh5UpperNum (a - b) (a + b) : ℝ) / (atanh5UpperDen (a - b) (a + b) : ℝ) := by
  have hbr : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hvr : (1 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
    rw [one_le_div hbr]; exact_mod_cast hba
  have hbnd := real_log_atanh_bounds 5 hvr
  set u := a - b
  set w := a + b
  have hu_cast : (u : ℝ) = (a : ℝ) - (b : ℝ) := Nat.cast_sub hba
  have hw_cast : (w : ℝ) = (a : ℝ) + (b : ℝ) := Nat.cast_add a b
  have hw_pos : (0 : ℝ) < (w : ℝ) := by
    rw [hw_cast]; linarith [show (b : ℝ) ≤ (a : ℝ) by exact_mod_cast hba]
  have hz_eq : ((a : ℝ) / (b : ℝ) - 1) / ((a : ℝ) / (b : ℝ) + 1) = (u : ℝ) / (w : ℝ) := by
    rw [hu_cast, hw_cast]; field_simp [hbr.ne', hw_pos.ne']
  have huw_lt : u * u < w * w := by
    have : u < w := by omega
    exact Nat.mul_lt_mul'' this this
  have hwu_cast : ((w * w - u * u : ℕ) : ℝ) = (w : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    rw [Nat.cast_sub huw_lt.le]; push_cast; ring
  have hwu_pos : (0 : ℝ) < (w : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
    have : (0 : ℕ) < w * w - u * u := Nat.sub_pos_of_lt huw_lt
    rw [← hwu_cast]; exact_mod_cast this
  have hpart :
      atanhPartial 5 ((u : ℝ) / (w : ℝ)) =
        (atanh5LowerNum u w : ℝ) / (atanh5Den w : ℝ) := by
    unfold atanhPartial atanh5LowerNum atanh5Den
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    push_cast
    field_simp [hw_pos.ne']
    ring
  have hup :
      atanhPartial 5 ((u : ℝ) / (w : ℝ)) + atanhTail 5 ((u : ℝ) / (w : ℝ)) =
        (atanh5UpperNum u w : ℝ) / (atanh5UpperDen u w : ℝ) := by
    rw [hpart]
    unfold atanhTail atanh5UpperNum atanh5UpperDen atanh5Den
    push_cast
    rw [hwu_cast]
    have h1z : 1 - ((u : ℝ) / (w : ℝ)) ^ 2 = ((w : ℝ) ^ 2 - (u : ℝ) ^ 2) / (w : ℝ) ^ 2 := by
      field_simp [hw_pos.ne']
    rw [h1z]
    field_simp [hw_pos.ne', hwu_pos.ne']
    ring
  rw [hz_eq, hpart] at hbnd
  constructor
  · exact hbnd.1
  · have h2 := hbnd.2
    rw [← hpart, hup] at h2
    exact h2

/-- Cleared-denominator `Nat` lower-bound soundness for `Real.log (a / b)`. -/
theorem atanh5_log_gt_of_nat {a b num den : ℕ} (hb : 0 < b) (hba : b ≤ a) (hden : 0 < den)
    (hnat : num * atanh5Den (a + b) < atanh5LowerNum (a - b) (a + b) * den) :
    (num : ℝ) / (den : ℝ) < Real.log ((a : ℝ) / (b : ℝ)) := by
  have h := (atanh5_real_bounds hb hba).1
  have hden_pos : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hw_pos : (0 : ℝ) < (atanh5Den (a + b) : ℝ) := by
    unfold atanh5Den
    have : 0 < a + b := by omega
    positivity
  have hlt : (num : ℝ) / (den : ℝ) < (atanh5LowerNum (a - b) (a + b) : ℝ) / (atanh5Den (a + b) : ℝ) := by
    rw [div_lt_div_iff₀ hden_pos hw_pos]
    exact_mod_cast hnat
  exact lt_of_lt_of_le hlt h

/-- Cleared-denominator `Nat` upper-bound soundness for `Real.log (a / b)`. -/
theorem atanh5_log_lt_of_nat {a b num den : ℕ} (hb : 0 < b) (hba : b ≤ a) (hden : 0 < den)
    (hnat : atanh5UpperNum (a - b) (a + b) * den < num * atanh5UpperDen (a - b) (a + b)) :
    Real.log ((a : ℝ) / (b : ℝ)) < (num : ℝ) / (den : ℝ) := by
  have h := (atanh5_real_bounds hb hba).2
  have hden_pos : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hup_pos : (0 : ℝ) < (atanh5UpperDen (a - b) (a + b) : ℝ) := by
    unfold atanh5UpperDen
    have h1 : 0 < a + b := by omega
    have h2 : (a - b) * (a - b) < (a + b) * (a + b) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    have h3 : 0 < (a + b) * (a + b) - (a - b) * (a - b) := Nat.sub_pos_of_lt h2
    positivity
  have hlt : (atanh5UpperNum (a - b) (a + b) : ℝ) / (atanh5UpperDen (a - b) (a + b) : ℝ) <
      (num : ℝ) / (den : ℝ) := by
    rw [div_lt_div_iff₀ hup_pos hden_pos]
    exact_mod_cast hnat
  exact lt_of_le_of_lt h hlt

private lemma real_log_two_10d :
    (6931471805 : ℝ) / 10 ^ 10 < Real.log 2 ∧ Real.log 2 < (6931471809 : ℝ) / 10 ^ 10 := by
  have h1lo := atanh5_log_gt_of_nat (a := 5) (b := 4) (num := 2231435513) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h1hi := atanh5_log_lt_of_nat (a := 5) (b := 4) (num := 2231435514) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2lo := atanh5_log_gt_of_nat (a := 128) (b := 125) (num := 237165266) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2hi := atanh5_log_lt_of_nat (a := 128) (b := 125) (num := 237165267) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have hdecomp : Real.log 2 = 3 * Real.log ((5 : ℝ) / 4) + Real.log ((128 : ℝ) / 125) := by
    have hpow : (3 : ℝ) * Real.log ((5 : ℝ) / 4) = Real.log (((5 : ℝ) / 4) ^ (3 : ℕ)) := by
      rw [Real.log_pow]; norm_num
    rw [hpow, ← Real.log_mul (by positivity) (by positivity)]
    norm_num
  rw [hdecomp]
  norm_num at h1lo h1hi h2lo h2hi ⊢
  constructor <;> linarith

private lemma real_log_three_10d :
    (10986122885 : ℝ) / 10 ^ 10 < Real.log 3 ∧ Real.log 3 < (10986122891 : ℝ) / 10 ^ 10 := by
  have h1lo := atanh5_log_gt_of_nat (a := 5) (b := 4) (num := 2231435513) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h1hi := atanh5_log_lt_of_nat (a := 5) (b := 4) (num := 2231435514) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2lo := atanh5_log_gt_of_nat (a := 128) (b := 125) (num := 237165266) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2hi := atanh5_log_lt_of_nat (a := 128) (b := 125) (num := 237165267) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h65lo := atanh5_log_gt_of_nat (a := 6) (b := 5) (num := 1823215567) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h65hi := atanh5_log_lt_of_nat (a := 6) (b := 5) (num := 1823215568) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have hdecomp : Real.log 3 = 4 * Real.log ((5 : ℝ) / 4) + Real.log ((128 : ℝ) / 125) +
      Real.log ((6 : ℝ) / 5) := by
    have hpow : (4 : ℝ) * Real.log ((5 : ℝ) / 4) = Real.log (((5 : ℝ) / 4) ^ (4 : ℕ)) := by
      rw [Real.log_pow]; norm_num
    rw [hpow, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    norm_num
  rw [hdecomp]
  norm_num at h1lo h1hi h2lo h2hi h65lo h65hi ⊢
  constructor <;> linarith

/-- High-precision enclosures for `ln 2` via `2 = (5/4)^3 * (128/125)` and `ln 3` via
`3 = 2 * (5/4) * (6/5)`, checked instantaneously by pure-`Nat` `decide +kernel`. -/
theorem real_log_two_bounds :
    (693147180 : ℝ) / 10 ^ 9 < Real.log 2 ∧ Real.log 2 < (693147181 : ℝ) / 10 ^ 9 := by
  have h := real_log_two_10d
  constructor <;> linarith only [h.1, h.2]

theorem real_log_three_bounds :
    (1098612288 : ℝ) / 10 ^ 9 < Real.log 3 ∧ Real.log 3 < (1098612290 : ℝ) / 10 ^ 9 := by
  have h := real_log_three_10d
  constructor <;> linarith only [h.1, h.2]

/-! ## 2. Exact Enclosures for `log_3 2`, Lagarias `H_2(log_3 2)`, and Tail Bounds -/

/-- Exact rational enclosure `0.63092975 < log_3 2 < 0.63092976` matching `P_RANGE` in Paper 1. -/
theorem log3_two_bounds :
    (63092975 : ℝ) / 10 ^ 8 < Real.log 2 / Real.log 3 ∧
    Real.log 2 / Real.log 3 < (63092976 : ℝ) / 10 ^ 8 := by
  have h2 := real_log_two_bounds
  have h3 := real_log_three_bounds
  have h3pos : 0 < Real.log 3 := by linarith
  constructor
  · rw [lt_div_iff₀ h3pos]
    have hmul : ((63092975 : ℝ) / 10 ^ 8) * Real.log 3 <
        ((63092975 : ℝ) / 10 ^ 8) * ((1098612290 : ℝ) / 10 ^ 9) :=
      mul_lt_mul_of_pos_left h3.2 (by norm_num)
    linarith [h2.1]
  · rw [div_lt_iff₀ h3pos]
    have hmul : ((63092976 : ℝ) / 10 ^ 8) * ((1098612288 : ℝ) / 10 ^ 9) <
        ((63092976 : ℝ) / 10 ^ 8) * Real.log 3 :=
      mul_lt_mul_of_pos_left h3.1 (by norm_num)
    linarith [h2.2]

/-- Soundness lemma linking pure-`Nat` 5-term `atanh` checks to `-Real.logb 2 (k / d)`. -/
theorem neg_logb2_nat_bounds {k d sh : ℕ} (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) :
    let a := d
    let b := k * 2 ^ sh
    (sh : ℝ) + ((atanh5LowerNum (a - b) (a + b) : ℝ) / (atanh5Den (a + b) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) ≤ -Real.logb 2 ((k : ℝ) / (d : ℝ)) ∧
    -Real.logb 2 ((k : ℝ) / (d : ℝ)) ≤
      (sh : ℝ) + ((atanh5UpperNum (a - b) (a + b) : ℝ) / (atanh5UpperDen (a - b) (a + b) : ℝ)) /
        ((693147180 : ℝ) / 10 ^ 9) := by
  intro a b
  have hb_pos : 0 < b := Nat.mul_pos hk (by positivity)
  have hd_pos : 0 < d := lt_of_lt_of_le hb_pos hred
  have hab_pos : (0 : ℝ) < (a : ℝ) / (b : ℝ) := by positivity
  have hab_ge1 : (1 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
    rw [one_le_div (Nat.cast_pos.mpr hb_pos)]; exact_mod_cast hred
  have hinv : ((k : ℝ) / (d : ℝ))⁻¹ = (2 : ℝ) ^ sh * ((a : ℝ) / (b : ℝ)) := by
    dsimp [a, b]; push_cast; field_simp [(Nat.cast_pos.mpr hk).ne', (Nat.cast_pos.mpr hd_pos).ne']
  have hneg : -Real.logb 2 ((k : ℝ) / (d : ℝ)) = (sh : ℝ) + Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 := by
    unfold Real.logb
    rw [← neg_div, ← Real.log_inv, hinv, Real.log_mul (by positivity) hab_pos.ne',
      Real.log_pow, add_div]
    have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [mul_div_cancel_right₀ _ hlog2ne]
  rw [hneg]
  have hatanh := atanh5_real_bounds hb_pos hred
  have hlog2 := real_log_two_bounds
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogv_nonneg : 0 ≤ Real.log ((a : ℝ) / (b : ℝ)) := Real.log_nonneg hab_ge1
  constructor
  · have h1 : ((atanh5LowerNum (a - b) (a + b) : ℝ) / (atanh5Den (a + b) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) ≤ Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 := by
      calc _ ≤ Real.log ((a : ℝ) / (b : ℝ)) / ((693147181 : ℝ) / 10 ^ 9) :=
            div_le_div_of_nonneg_right hatanh.1 (by norm_num)
        _ ≤ Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 :=
            div_le_div_of_nonneg_left hlogv_nonneg hlog2_pos hlog2.2.le
    linarith
  · have h2 : Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 ≤
        ((atanh5UpperNum (a - b) (a + b) : ℝ) / (atanh5UpperDen (a - b) (a + b) : ℝ)) /
        ((693147180 : ℝ) / 10 ^ 9) := by
      calc _ ≤ ((atanh5UpperNum (a - b) (a + b) : ℝ) / (atanh5UpperDen (a - b) (a + b) : ℝ)) /
              Real.log 2 := div_le_div_of_nonneg_right hatanh.2 hlog2_pos.le
        _ ≤ _ := div_le_div_of_nonneg_left (hlogv_nonneg.trans hatanh.2) (by norm_num) hlog2.1.le
    linarith

/-- Cleared-denominator `Nat` lower-bound soundness for `-Real.logb 2 (k / d)`. -/
theorem neg_logb2_ge_of_nat {k d sh loNum scale : ℕ}
    (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) (hscale : 0 < scale) (hsh : sh * scale ≤ loNum)
    (hnat : (loNum - sh * scale) * atanh5Den (d + k * 2 ^ sh) * 693147181 ≤
      atanh5LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) * (scale * 10 ^ 9)) :
    (loNum : ℝ) / (scale : ℝ) ≤ -Real.logb 2 ((k : ℝ) / (d : ℝ)) := by
  have hb := (neg_logb2_nat_bounds hk hred).1
  have hsc_pos : (0 : ℝ) < (scale : ℝ) := Nat.cast_pos.mpr hscale
  have hden_pos : (0 : ℝ) < (atanh5Den (d + k * 2 ^ sh) : ℝ) := by
    unfold atanh5Den
    have : 0 < d + k * 2 ^ sh := by have := Nat.mul_pos hk (by positivity : 0 < 2 ^ sh); omega
    positivity
  have hsub_cast : ((loNum - sh * scale : ℕ) : ℝ) = (loNum : ℝ) - (sh : ℝ) * (scale : ℝ) := by
    rw [Nat.cast_sub hsh]; push_cast; rfl
  have hnat_r : ((loNum : ℝ) - (sh : ℝ) * (scale : ℝ)) * (atanh5Den (d + k * 2 ^ sh) : ℝ) *
      693147181 ≤ (atanh5LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * ((scale : ℝ) * 10 ^ 9) := by
    rw [← hsub_cast]; exact_mod_cast hnat
  have hdiv : (loNum : ℝ) / (scale : ℝ) - (sh : ℝ) ≤
      ((atanh5LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) / (atanh5Den (d + k * 2 ^ sh) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) := by
    have h1 : (loNum : ℝ) / (scale : ℝ) - (sh : ℝ) =
        ((loNum : ℝ) - (sh : ℝ) * (scale : ℝ)) / (scale : ℝ) := by field_simp [hsc_pos.ne']
    have h2 : ((atanh5LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh5Den (d + k * 2 ^ sh) : ℝ)) / ((693147181 : ℝ) / 10 ^ 9) =
        ((atanh5LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 10 ^ 9) /
        ((atanh5Den (d + k * 2 ^ sh) : ℝ) * 693147181) := by field_simp [hden_pos.ne']
    rw [h1, h2, div_le_div_iff₀ hsc_pos (by positivity)]
    linarith
  linarith

/-- Cleared-denominator `Nat` upper-bound soundness for `-Real.logb 2 (k / d)`. -/
theorem neg_logb2_le_of_nat {k d sh hiNum scale : ℕ}
    (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) (hscale : 0 < scale) (hsh : sh * scale ≤ hiNum)
    (hnat : atanh5UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) * (scale * 10 ^ 9) ≤
      (hiNum - sh * scale) * atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) * 693147180) :
    -Real.logb 2 ((k : ℝ) / (d : ℝ)) ≤ (hiNum : ℝ) / (scale : ℝ) := by
  have hb := (neg_logb2_nat_bounds hk hred).2
  have hsc_pos : (0 : ℝ) < (scale : ℝ) := Nat.cast_pos.mpr hscale
  have hb_pos : 0 < k * 2 ^ sh := Nat.mul_pos hk (by positivity)
  have hden_pos : (0 : ℝ) < (atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) := by
    unfold atanh5UpperDen
    have h1 : 0 < d + k * 2 ^ sh := by omega
    have h2 : (d - k * 2 ^ sh) * (d - k * 2 ^ sh) < (d + k * 2 ^ sh) * (d + k * 2 ^ sh) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    have h3 : 0 < (d + k * 2 ^ sh) * (d + k * 2 ^ sh) - (d - k * 2 ^ sh) * (d - k * 2 ^ sh) :=
      Nat.sub_pos_of_lt h2
    positivity
  have hsub_cast : ((hiNum - sh * scale : ℕ) : ℝ) = (hiNum : ℝ) - (sh : ℝ) * (scale : ℝ) := by
    rw [Nat.cast_sub hsh]; push_cast; rfl
  have hnat_r : (atanh5UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * ((scale : ℝ) * 10 ^ 9) ≤
      ((hiNum : ℝ) - (sh : ℝ) * (scale : ℝ)) *
        (atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 693147180 := by
    rw [← hsub_cast]; exact_mod_cast hnat
  have hdiv : ((atanh5UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ)) / ((693147180 : ℝ) / 10 ^ 9) ≤
      (hiNum : ℝ) / (scale : ℝ) - (sh : ℝ) := by
    have h1 : (hiNum : ℝ) / (scale : ℝ) - (sh : ℝ) =
        ((hiNum : ℝ) - (sh : ℝ) * (scale : ℝ)) / (scale : ℝ) := by field_simp [hsc_pos.ne']
    have h2 : ((atanh5UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ)) / ((693147180 : ℝ) / 10 ^ 9) =
        ((atanh5UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 10 ^ 9) /
        ((atanh5UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 693147180) := by
      field_simp [hden_pos.ne']
    rw [h1, h2, div_le_div_iff₀ (by positivity) hsc_pos]
    linarith
  linarith

/-- High-product tail bound (`classical-tilted-passage.md`, `explicit-shell-count.md`):
for `p = log_3 2` and tilt `z = 64 / 100`, `B(1, 1.012 * p; 0.64) < 0.943928`. -/
theorem high_product_tail_bound :
    crossEntropy 1 ((1012 / 1000 : ℝ) * (Real.log 2 / Real.log 3)) (64 / 100) <
      943928 / 10 ^ 6 := by
  have hp := log3_two_bounds
  have hc1 := neg_logb2_le_of_nat (k := 16) (d := 25) (sh := 0) (hiNum := 6438562) (scale := 10 ^ 7)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hc2 := neg_logb2_le_of_nat (k := 9) (d := 25) (sh := 1) (hiNum := 14739312) (scale := 10 ^ 7)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hc1r : -Real.logb 2 (64 / 100 : ℝ) ≤ 6438562 / 10 ^ 7 := by
    norm_num at hc1
    have hcast : (16 / 25 : ℝ) = 64 / 100 := by norm_num
    rw [hcast] at hc1; linarith only [hc1]
  have hc2r : -Real.logb 2 (1 - 64 / 100 : ℝ) ≤ 14739312 / 10 ^ 7 := by
    norm_num at hc2
    have hcast : (9 / 25 : ℝ) = 1 - 64 / 100 := by norm_num
    rw [hcast] at hc2; linarith only [hc2]
  have hmono : -Real.logb 2 (64 / 100 : ℝ) ≤ -Real.logb 2 (1 - 64 / 100 : ℝ) := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 - 64 / 100) (by norm_num : 1 - (64 / 100 : ℝ) ≤ 64 / 100)
    linarith only [hlog]
  have hj_ge : (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8) ≤
      (1012 / 1000 : ℝ) * (Real.log 2 / Real.log 3) :=
    mul_le_mul_of_nonneg_left hp.1.le (by norm_num)
  unfold crossEntropy
  have hstep :
      (1012 / 1000 : ℝ) * (Real.log 2 / Real.log 3) * (-Real.logb 2 (64 / 100 : ℝ)) +
        (1 - (1012 / 1000 : ℝ) * (Real.log 2 / Real.log 3)) * (-Real.logb 2 (1 - 64 / 100 : ℝ)) ≤
      (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8) * (-Real.logb 2 (64 / 100 : ℝ)) +
        (1 - (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8)) * (-Real.logb 2 (1 - 64 / 100 : ℝ)) := by
    have hdiff : 0 ≤ ((1012 / 1000 : ℝ) * (Real.log 2 / Real.log 3) -
          (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8)) *
        ((-Real.logb 2 (1 - 64 / 100 : ℝ)) - (-Real.logb 2 (64 / 100 : ℝ))) :=
      mul_nonneg (by linarith only [hj_ge]) (by linarith only [hmono])
    linarith only [hdiff]
  have h1 : (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8) * (-Real.logb 2 (64 / 100 : ℝ)) ≤
      (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8) * (6438562 / 10 ^ 7) :=
    mul_le_mul_of_nonneg_left hc1r (by norm_num)
  have h2 : (1 - (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8)) * (-Real.logb 2 (1 - 64 / 100 : ℝ)) ≤
      (1 - (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8)) * (14739312 / 10 ^ 7) :=
    mul_le_mul_of_nonneg_left hc2r (by norm_num)
  have hnum : (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8) * (6438562 / 10 ^ 7) +
      (1 - (1012 / 1000 : ℝ) * (63092975 / 10 ^ 8)) * (14739312 / 10 ^ 7) < 943928 / 10 ^ 6 := by
    norm_num
  exact lt_of_le_of_lt (hstep.trans (add_le_add h1 h2)) hnum

/-- Exact Lagarias (1985) all-shell tilt bound (`explicit-shell-count.md`):
for `p = log_3 2`, `e = 10^{-7}`, and tilt `z = 0.63093`,
`B(1, (1 - e) * p; 0.63093) < 0.94995558`. -/
theorem all_shell_lagarias_tilt_bound :
    crossEntropy 1 ((1 - (1 : ℝ) / 10 ^ 7) * (Real.log 2 / Real.log 3)) (63093 / 10 ^ 5) <
      94995558 / 10 ^ 8 := by
  have h2 := real_log_two_10d
  have h3 := real_log_three_10d
  have h3pos : 0 < Real.log 3 := by linarith only [h3.1]
  have hp_lo9 : (630929753 : ℝ) / 10 ^ 9 < Real.log 2 / Real.log 3 := by
    rw [lt_div_iff₀ h3pos]
    have hmul : ((630929753 : ℝ) / 10 ^ 9) * Real.log 3 <
        ((630929753 : ℝ) / 10 ^ 9) * ((10986122891 : ℝ) / 10 ^ 10) :=
      mul_lt_mul_of_pos_left h3.2 (by norm_num)
    have hnum : ((630929753 : ℝ) / 10 ^ 9) * ((10986122891 : ℝ) / 10 ^ 10) <
        (6931471805 : ℝ) / 10 ^ 10 := by norm_num
    exact lt_trans (lt_trans hmul hnum) h2.1
  have h1a := atanh5_log_lt_of_nat (a := 200000) (b := 189279) (num := 550952496) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2a := atanh5_log_lt_of_nat (a := 150000) (b := 147628) (num := 159396981) (den := 10 ^ 10)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have hlog_p : Real.log ((100000 : ℝ) / 63093) =
      Real.log 3 - Real.log 2 + Real.log ((200000 : ℝ) / 189279) := by
    rw [← Real.log_div (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlog_q : Real.log ((100000 : ℝ) / 36907) =
      3 * Real.log 2 - Real.log 3 + Real.log ((150000 : ℝ) / 147628) := by
    have hpow : (3 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (3 : ℕ)) := by rw [Real.log_pow]; norm_num
    rw [hpow, ← Real.log_div (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlogp_lt : Real.log ((100000 : ℝ) / 63093) < 4605603582 / 10 ^ 10 := by
    norm_num at h1a; linarith only [hlog_p, h3.2, h2.1, h1a]
  have hlogq_lt : Real.log ((100000 : ℝ) / 36907) < 9967689523 / 10 ^ 10 := by
    norm_num at h2a; linarith only [hlog_q, h2.2, h3.1, h2a]
  have hc1r : -Real.logb 2 (63093 / 10 ^ 5 : ℝ) < 664448145 / 10 ^ 9 := by
    unfold Real.logb
    rw [← neg_div, ← Real.log_inv]
    have hinv : ((63093 / 10 ^ 5 : ℝ))⁻¹ = (100000 : ℝ) / 63093 := by norm_num
    rw [hinv, div_lt_iff₀ (Real.log_pos (by norm_num))]
    have hmul : (664448145 / 10 ^ 9 : ℝ) * ((6931471805 : ℝ) / 10 ^ 10) <
        (664448145 / 10 ^ 9 : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_left h2.1 (by norm_num)
    have hnum : (4605603582 / 10 ^ 10 : ℝ) <
        (664448145 / 10 ^ 9 : ℝ) * ((6931471805 : ℝ) / 10 ^ 10) := by norm_num
    exact lt_trans (lt_trans hlogp_lt hnum) hmul
  have hc2r : -Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ) < 1438033625 / 10 ^ 9 := by
    unfold Real.logb
    rw [← neg_div, ← Real.log_inv]
    have hinv : (1 - (63093 / 10 ^ 5 : ℝ))⁻¹ = (100000 : ℝ) / 36907 := by norm_num
    rw [hinv, div_lt_iff₀ (Real.log_pos (by norm_num))]
    have hmul : (1438033625 / 10 ^ 9 : ℝ) * ((6931471805 : ℝ) / 10 ^ 10) <
        (1438033625 / 10 ^ 9 : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_left h2.1 (by norm_num)
    have hnum : (9967689523 / 10 ^ 10 : ℝ) <
        (1438033625 / 10 ^ 9 : ℝ) * ((6931471805 : ℝ) / 10 ^ 10) := by norm_num
    exact lt_trans (lt_trans hlogq_lt hnum) hmul
  have hmono : -Real.logb 2 (63093 / 10 ^ 5 : ℝ) ≤ -Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ) := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 - 63093 / 10 ^ 5) (by norm_num : 1 - (63093 / 10 ^ 5 : ℝ) ≤ 63093 / 10 ^ 5)
    linarith only [hlog]
  have hj_ge : (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9) ≤
      (1 - (1 : ℝ) / 10 ^ 7) * (Real.log 2 / Real.log 3) :=
    mul_le_mul_of_nonneg_left hp_lo9.le (by norm_num)
  unfold crossEntropy
  have hstep :
      (1 - (1 : ℝ) / 10 ^ 7) * (Real.log 2 / Real.log 3) * (-Real.logb 2 (63093 / 10 ^ 5 : ℝ)) +
        (1 - (1 - (1 : ℝ) / 10 ^ 7) * (Real.log 2 / Real.log 3)) *
          (-Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ)) ≤
      (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9) * (-Real.logb 2 (63093 / 10 ^ 5 : ℝ)) +
        (1 - (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9)) *
          (-Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ)) := by
    have hdiff : 0 ≤ ((1 - (1 : ℝ) / 10 ^ 7) * (Real.log 2 / Real.log 3) -
          (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9)) *
        ((-Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ)) - (-Real.logb 2 (63093 / 10 ^ 5 : ℝ))) :=
      mul_nonneg (by linarith only [hj_ge]) (by linarith only [hmono])
    linarith only [hdiff]
  have h1 : (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9) * (-Real.logb 2 (63093 / 10 ^ 5 : ℝ)) <
      (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9) * (664448145 / 10 ^ 9) :=
    mul_lt_mul_of_pos_left hc1r (by norm_num)
  have h2' : (1 - (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9)) * (-Real.logb 2 (1 - 63093 / 10 ^ 5 : ℝ)) <
      (1 - (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9)) * (1438033625 / 10 ^ 9) :=
    mul_lt_mul_of_pos_left hc2r (by norm_num)
  have hnum : (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9) * (664448145 / 10 ^ 9) +
      (1 - (1 - (1 : ℝ) / 10 ^ 7) * (630929753 / 10 ^ 9)) * (1438033625 / 10 ^ 9) <
        94995558 / 10 ^ 8 := by
    norm_num
  exact lt_of_le_of_lt hstep (lt_trans (add_lt_add h1 h2') hnum)

/-- Lagarias (1985) Theorem F binary entropy enclosure: `0.949955 < H_2(log_3 2) < 0.949956`. -/
theorem lagarias_entropy_bounds :
    949955 / 10 ^ 6 < binEntropy (Real.log 2 / Real.log 3) ∧
    binEntropy (Real.log 2 / Real.log 3) < 949956 / 10 ^ 6 := by
  have hp := log3_two_bounds
  set p := Real.log 2 / Real.log 3
  have hp_pos : 0 < p := by linarith only [hp.1]
  have h1p_pos : 0 < 1 - p := by linarith only [hp.2]
  have hlo_p := neg_logb2_ge_of_nat (k := 63092976) (d := 10 ^ 8) (sh := 0)
    (loNum := 6644486) (scale := 10 ^ 7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hhi_p := neg_logb2_le_of_nat (k := 63092975) (d := 10 ^ 8) (sh := 0)
    (hiNum := 6644488) (scale := 10 ^ 7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hlo_q := neg_logb2_ge_of_nat (k := 36907025) (d := 10 ^ 8) (sh := 1)
    (loNum := 14380326) (scale := 10 ^ 7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hhi_q := neg_logb2_le_of_nat (k := 36907024) (d := 10 ^ 8) (sh := 1)
    (hiNum := 14380327) (scale := 10 ^ 7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hnlp_ge : 6644486 / 10 ^ 7 ≤ -Real.logb 2 p := by
    have h2 : Real.logb 2 p ≤ Real.logb 2 ((63092976 : ℝ) / (10 ^ 8 : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) hp_pos (by linarith only [hp.2])
    norm_num at hlo_p ⊢; linarith only [hlo_p, h2]
  have hnlp_le : -Real.logb 2 p ≤ 6644488 / 10 ^ 7 := by
    have h2 : Real.logb 2 ((63092975 : ℝ) / (10 ^ 8 : ℝ)) ≤ Real.logb 2 p :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith only [hp.1])
    norm_num at hhi_p ⊢; linarith only [hhi_p, h2]
  have hnlq_ge : 14380326 / 10 ^ 7 ≤ -Real.logb 2 (1 - p) := by
    have h2 : Real.logb 2 (1 - p) ≤ Real.logb 2 ((36907025 : ℝ) / (10 ^ 8 : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) h1p_pos (by linarith only [hp.1])
    norm_num at hlo_q ⊢; linarith only [hlo_q, h2]
  have hnlq_le : -Real.logb 2 (1 - p) ≤ 14380327 / 10 ^ 7 := by
    have h2 : Real.logb 2 ((36907024 : ℝ) / (10 ^ 8 : ℝ)) ≤ Real.logb 2 (1 - p) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith only [hp.2])
    norm_num at hhi_q ⊢; linarith only [hhi_q, h2]
  unfold binEntropy crossEntropy
  constructor
  · have h1 : (63092975 / 10 ^ 8 : ℝ) * (6644486 / 10 ^ 7) ≤ p * (-Real.logb 2 p) :=
      mul_le_mul hp.1.le hnlp_ge (by norm_num) hp_pos.le
    have h2 : (36907024 / 10 ^ 8 : ℝ) * (14380326 / 10 ^ 7) ≤ (1 - p) * (-Real.logb 2 (1 - p)) :=
      mul_le_mul (by linarith only [hp.2]) hnlq_ge (by norm_num) h1p_pos.le
    have hnum : (949955 / 10 ^ 6 : ℝ) <
        (63092975 / 10 ^ 8 : ℝ) * (6644486 / 10 ^ 7) +
          (36907024 / 10 ^ 8 : ℝ) * (14380326 / 10 ^ 7) := by norm_num
    exact lt_of_lt_of_le hnum (add_le_add h1 h2)
  · have h1 : p * (-Real.logb 2 p) ≤ (63092976 / 10 ^ 8 : ℝ) * (6644488 / 10 ^ 7) :=
      mul_le_mul hp.2.le hnlp_le (by linarith only [hnlp_ge]) (by norm_num)
    have h2 : (1 - p) * (-Real.logb 2 (1 - p)) ≤ (36907025 / 10 ^ 8 : ℝ) * (14380327 / 10 ^ 7) :=
      mul_le_mul (by linarith only [hp.1]) hnlq_le (by linarith only [hnlq_ge]) (by norm_num)
    have hnum : (63092976 / 10 ^ 8 : ℝ) * (6644488 / 10 ^ 7) +
        (36907025 / 10 ^ 8 : ℝ) * (14380327 / 10 ^ 7) < (949956 / 10 ^ 6 : ℝ) := by norm_num
    exact lt_of_le_of_lt (add_le_add h1 h2) hnum

/-! ## 3. Shorter-Window `0.0516` Fixed-Height Margin Certificate -/

/-- Pure-kernel verification of the `0.0516` fixed-height shell saving certificate
(`separated-suffix-collisions.md`, `check_balanced_collisions.py`). -/
theorem shorter_window_00516_margin :
    let tau : ℚ := 485 / 1000
    let split : ℚ := 4882501 / 10000000
    let suffix : ℚ := 1 - split
    let excess : ℚ := 32 / 10000
    let peak : ℚ := 26 / 1000
    let loss : ℚ := 1 / 10000000
    let low : ℚ := 25237 / 40000
    let u : ℚ := 7 / 10
    let far : ℚ := (51 / 1000) * (3 / 10) * suffix - (95 / 100) * (split - tau) - loss
    let near : ℚ := (9499 / 10000) * tau - (882 / 1000) * suffix - (3 / 2) * loss
    let headroom : ℚ := 2 * low ^ 2 * peak ^ 2 / (split * u) - loss / 2
    let net : ℚ := min ((488 / 1000) * excess) (min ((min far near - (excess + loss) / 2) / 2) headroom)
    split - (tau + excess + loss) = 1 / 20000 ∧
    1 + peak < (1 - tau) + suffix ∧
    1 + u + u ^ 2 / 2 + u ^ 3 / 6 > 2 ∧
    (1 - 94996 / 100000) + net > 516 / 10000 := by
  norm_num

/-- Real-valued verification of the entropy and coupling constants used in the `0.0516` proof:
`H_2(3/10) < 0.882`, `-log_2(2 √(p(1-p))) > 0.051`, `p * log_2(p/(1-p)) > 0.488`, and `ln 2 < 7/10`. -/
theorem shorter_window_00516_real_constants :
    binEntropy (3 / 10 : ℝ) < 882 / 1000 ∧
    Real.log 2 < 7 / 10 ∧
    (25237 / 40000 : ℝ) < Real.log 2 / Real.log 3 ∧
    (488 / 1000 : ℝ) < (Real.log 2 / Real.log 3) *
      Real.logb 2 ((Real.log 2 / Real.log 3) / (1 - Real.log 2 / Real.log 3)) ∧
    (51 / 1000 : ℝ) < -Real.logb 2 (2 * Real.sqrt ((Real.log 2 / Real.log 3) *
      (1 - Real.log 2 / Real.log 3))) := by
  have hlog2 := real_log_two_bounds
  have hp := log3_two_bounds
  set p := Real.log 2 / Real.log 3
  have hH310 : binEntropy (3 / 10 : ℝ) < 882 / 1000 := by
    have h1 := neg_logb2_le_of_nat (k := 3) (d := 10) (sh := 1) (hiNum := 1737) (scale := 1000)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    have h2 := neg_logb2_le_of_nat (k := 7) (d := 10) (sh := 0) (hiNum := 515) (scale := 1000)
      (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    norm_num at h1 h2
    have h2r : -Real.logb 2 (1 - 3 / 10 : ℝ) ≤ 515 / 1000 := by
      have hcast : (7 / 10 : ℝ) = 1 - 3 / 10 := by norm_num
      rw [hcast] at h2; linarith only [h2]
    unfold binEntropy crossEntropy
    linarith only [h1, h2r]
  have ha_gt : (488 / 1000 : ℝ) < p * Real.logb 2 (p / (1 - p)) := by
    have hrat : (3419 / 2000 : ℝ) ≤ p / (1 - p) := by
      rw [le_div_iff₀ (by linarith only [hp.2])]
      linarith only [hp.1]
    have hlo := atanh5_log_gt_of_nat (a := 3419) (b := 2000) (num := 5362) (den := 10000)
      (by decide) (by decide) (by decide) (by decide +kernel)
    have hlog_ge : (5362 / 10000 : ℝ) < Real.log (p / (1 - p)) := by
      have h2 : Real.log ((3419 : ℝ) / (2000 : ℝ)) ≤ Real.log (p / (1 - p)) :=
        Real.log_le_log (by norm_num) hrat
      norm_num at hlo; linarith only [hlo, h2]
    have hlogb_ge : (7735 / 10000 : ℝ) < Real.logb 2 (p / (1 - p)) := by
      unfold Real.logb
      rw [lt_div_iff₀ (Real.log_pos (by norm_num))]
      have hmul : (7735 / 10000 : ℝ) * Real.log 2 <
          (7735 / 10000 : ℝ) * ((693147181 : ℝ) / 10 ^ 9) :=
        mul_lt_mul_of_pos_left hlog2.2 (by norm_num)
      have hnum : (7735 / 10000 : ℝ) * ((693147181 : ℝ) / 10 ^ 9) < 5362 / 10000 := by norm_num
      exact lt_trans (lt_trans hmul hnum) hlog_ge
    have hmul : (63092975 / 10 ^ 8 : ℝ) * (7735 / 10000 : ℝ) < p * Real.logb 2 (p / (1 - p)) :=
      mul_lt_mul'' hp.1 hlogb_ge (by norm_num) (by norm_num)
    have hnum : (488 / 1000 : ℝ) < (63092975 / 10 ^ 8 : ℝ) * (7735 / 10000 : ℝ) := by norm_num
    exact lt_trans hnum hmul
  have hc_gt : (51 / 1000 : ℝ) < -Real.logb 2 (2 * Real.sqrt (p * (1 - p))) := by
    have hpq_le : 4 * (p * (1 - p)) ≤ 9315 / 10000 := by
      have h1 : p ≤ 63092976 / 10 ^ 8 := hp.2.le
      have h2 : 1 - p ≤ 36907025 / 10 ^ 8 := by linarith only [hp.1]
      have hmul := mul_le_mul h1 h2 (by linarith only [hp.2]) (by norm_num)
      have hnum : 4 * ((63092976 / 10 ^ 8 : ℝ) * (36907025 / 10 ^ 8)) ≤ 9315 / 10000 := by norm_num
      linarith only [hmul, hnum]
    have hpq_pos : 0 < p * (1 - p) := mul_pos (by linarith only [hp.1]) (by linarith only [hp.2])
    have hsq : (2 * Real.sqrt (p * (1 - p))) ^ 2 = 4 * (p * (1 - p)) := by
      rw [mul_pow, Real.sq_sqrt hpq_pos.le]; norm_num
    have hlog_sq : 2 * Real.logb 2 (2 * Real.sqrt (p * (1 - p))) =
        Real.logb 2 (4 * (p * (1 - p))) := by
      rw [← hsq, Real.logb_pow]; ring
    have hlo_inv := neg_logb2_ge_of_nat (k := 1863) (d := 2000) (sh := 0)
      (loNum := 1023) (scale := 10000) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    norm_num at hlo_inv
    have h2 : Real.logb 2 (4 * (p * (1 - p))) ≤ Real.logb 2 (1863 / 2000 : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith only [hpq_le])
    linarith only [hlog_sq, hlo_inv, h2]
  refine ⟨hH310, by linarith only [hlog2.2], by linarith only [hp.1], ha_gt, hc_gt⟩

/-! ## 4. Separation-Band Thresholds and Evertse–Ferretti Line-Count Bounds -/

/-- Exact rational checks from `check_separation_bands.py` for the tight split
(`σ = 10^{-7}`, `k_* = 2^28`). -/
theorem separation_bands_tight_cert :
    let k : ℚ := 2 ^ 28
    let e : ℚ := 1 / 10 ^ 7
    let sigma : ℚ := 1 / 10 ^ 7
    let delta : ℚ := sigma / 2
    let tau : ℚ := 492 / 1000
    let beta : ℚ := 1 - tau
    let maxExcess : ℚ := 12 / 1000
    let lower : ℚ := 49597 / 100000
    let upper : ℚ := 150801 / 100000
    beta * k - 1 ≥ 3 ∧
    1 + 28 < (tau - e) * k ∧
    (beta - tau - maxExcess - 3 * e - sigma) * k ≥ 2 ∧
    k ≥ 8 / delta ∧
    28 + 2 ≤ (beta - maxExcess - e - lower) * k ∧
    4 ≤ (upper - (2 - tau)) * k ∧
    28 + 6 ≤ (2 * e + sigma - delta * upper) * k ∧
    upper / lower < 3041 / 1000 ∧
    (2 : ℚ) ^ 52 * 3 ^ 6 / delta ^ 2 = 1313249651341236633600000000000000 := by
  norm_num

/-- Exact rational checks from `check_separation_bands.py` for the wide split
(`σ = 10^{-4}`, `k_* = 2^20`). -/
theorem separation_bands_wide_cert :
    let k : ℚ := 2 ^ 20
    let e : ℚ := 1 / 10 ^ 7
    let sigma : ℚ := 1 / 10 ^ 4
    let delta : ℚ := sigma / 2
    let tau : ℚ := 492 / 1000
    let beta : ℚ := 1 - tau
    let maxExcess : ℚ := 12 / 1000
    let lower : ℚ := 49597 / 100000
    let upper : ℚ := 150801 / 100000
    beta * k - 1 ≥ 3 ∧
    1 + 20 < (tau - e) * k ∧
    (beta - tau - maxExcess - 3 * e - sigma) * k ≥ 2 ∧
    k ≥ 8 / delta ∧
    20 + 2 ≤ (beta - maxExcess - e - lower) * k ∧
    4 ≤ (upper - (2 - tau)) * k ∧
    20 + 6 ≤ (2 * e + sigma - delta * upper) * k ∧
    upper / lower < 3041 / 1000 ∧
    (2 : ℚ) ^ 52 * 3 ^ 6 / delta ^ 2 = 1313249651341236633600000000 := by
  norm_num

/-- Helper: `(27 / 10)^n > x` implies `Real.log x < n` (using `Real.exp 1 > 27 / 10`). -/
theorem real_log_lt_of_base_27_10 {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hpow : x < ((27 : ℝ) / 10) ^ n) :
    Real.log x < (n : ℝ) := by
  have he : (27 : ℝ) / 10 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h1 : x < (Real.exp 1) ^ n := lt_of_lt_of_le hpow (pow_le_pow_left₀ (by norm_num) he.le n)
  rw [← Real.exp_nat_mul, mul_one] at h1
  exact (Real.log_lt_iff_lt_exp hx).mpr h1

/-- **Evertse–Ferretti (2013) Theorem 3.1 Tight Line-Count Bound (`< 10^{58}`):**
At `σ = 10^{-7}`, `Q = 2 / σ = 20,000,000`, `k_* = 2^{28}`, both the exact rational certificate
(`check_absolute_line_count.py`) and the real-valued Evertse–Ferretti line count hold strictly
below `10^{58}`. -/
theorem evertse_ferretti_line_count_tight :
    let Q : ℕ := 20000000
    (495 : ℚ) / 1000 * (2 ^ 28 : ℚ) ≥ 4 * (Q : ℚ) ∧
    ((27 : ℚ) / 10) ^ 3 > 9 ∧
    ((27 : ℚ) / 10) ^ 20 > 18 * (Q : ℚ) ∧
    ((27 : ℚ) / 10) ^ 19 > 6 * (Q : ℚ) ∧
    4 * Nat.choose (32 * Q + 10) 2 * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 * 20 * 19 < 10 ^ 58 ∧
    (4 : ℝ) * (Nat.choose (32 * Q + 10) 2 : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
      Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < (10 : ℝ) ^ 58 := by
  intro Q
  have h1 : (495 : ℚ) / 1000 * (2 ^ 28 : ℚ) ≥ 4 * (Q : ℚ) := by norm_num [Q]
  have h2 : ((27 : ℚ) / 10) ^ 3 > 9 := by norm_num
  have h3 : ((27 : ℚ) / 10) ^ 20 > 18 * (Q : ℚ) := by norm_num [Q]
  have h4 : ((27 : ℚ) / 10) ^ 19 > 6 * (Q : ℚ) := by norm_num [Q]
  have hC_eq := Nat.choose_two_right (32 * Q + 10)
  have h5 : 4 * Nat.choose (32 * Q + 10) 2 * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 * 20 * 19 < 10 ^ 58 := by
    rw [hC_eq]; norm_num [Q]
  have hlog9 : Real.log 9 < 3 :=
    real_log_lt_of_base_27_10 (by norm_num) (by norm_num)
  have hlog1 : Real.log (18 * (Q : ℝ)) < 20 :=
    real_log_lt_of_base_27_10 (by positivity) (by norm_num [Q])
  have hlog2 : Real.log (2 * (Q : ℝ) * Real.log 9) < 19 := by
    have hlog9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have hQpos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]
    have harg_lt : 2 * (Q : ℝ) * Real.log 9 < 6 * (Q : ℝ) := by
      have h1'' := mul_lt_mul_of_pos_left hlog9 (by positivity : (0 : ℝ) < 2 * (Q : ℝ))
      linarith
    have h1' : Real.log (2 * (Q : ℝ) * Real.log 9) < Real.log (6 * (Q : ℝ)) :=
      Real.log_lt_log (by positivity) harg_lt
    have h2' : Real.log (6 * (Q : ℝ)) < 19 :=
      real_log_lt_of_base_27_10 (by positivity) (by norm_num [Q])
    linarith
  have hlog1_pos : 0 < Real.log (18 * (Q : ℝ)) := Real.log_pos (by norm_num [Q])
  have hlog2_pos : 0 < Real.log (2 * (Q : ℝ) * Real.log 9) := by
    apply Real.log_pos
    have hlog9_gt1 : 1 < Real.log 9 := by
      have h9 : Real.exp 1 < 9 := by linarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr h9
    have hQge : (1 : ℝ) ≤ (Q : ℝ) := by norm_num [Q]
    calc (1 : ℝ) < 2 * 1 * 1 := by norm_num
      _ ≤ 2 * (Q : ℝ) * Real.log 9 := by
        have hmul1 : (2 : ℝ) * 1 ≤ 2 * (Q : ℝ) := by linarith
        exact mul_le_mul hmul1 hlog9_gt1.le (by norm_num) (by linarith)
  have hreal :
      (4 : ℝ) * (Nat.choose (32 * Q + 10) 2 : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
        Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < (10 : ℝ) ^ 58 := by
    have hC_pos : 0 < Nat.choose (32 * Q + 10) 2 := by rw [hC_eq]; norm_num [Q]
    generalize Nat.choose (32 * Q + 10) 2 = C at h5 hC_pos ⊢
    have h5r : ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) * (20 * 19 : ℝ) <
        (10 : ℝ) ^ 58 := by
      have h5' : (4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3) * (20 * 19) < 10 ^ 58 := by
        simpa [mul_assoc] using h5
      exact_mod_cast h5'
    have hQpos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]
    have hcoeff_pos : (0 : ℝ) < ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) := by
      have : 0 < 4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 := by
        have : 0 < Q := by norm_num [Q]
        positivity
      exact_mod_cast this
    have hprod_lt : Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < 20 * 19 :=
      mul_lt_mul'' hlog1 hlog2 hlog1_pos.le hlog2_pos.le
    have hcast_lhs :
        (4 : ℝ) * (C : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
            Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) =
          ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) *
            (Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9)) := by
      push_cast; ring
    rw [hcast_lhs]
    exact lt_trans (mul_lt_mul_of_pos_left hprod_lt hcoeff_pos) h5r
  exact ⟨h1, h2, h3, h4, h5, hreal⟩

/-- **Evertse–Ferretti (2013) Theorem 3.1 Wide Line-Count Bound (`< 10^{43}`):**
At `σ = 10^{-4}`, `Q = 2 / σ = 20,000`, `k_* = 2^{20}`, both the exact rational certificate
(`check_absolute_line_count.py`) and the real-valued Evertse–Ferretti line count hold strictly
below `10^{43}`. -/
theorem evertse_ferretti_line_count_wide :
    let Q : ℕ := 20000
    (495 : ℚ) / 1000 * (2 ^ 20 : ℚ) ≥ 4 * (Q : ℚ) ∧
    ((27 : ℚ) / 10) ^ 3 > 9 ∧
    ((27 : ℚ) / 10) ^ 13 > 18 * (Q : ℚ) ∧
    ((27 : ℚ) / 10) ^ 12 > 6 * (Q : ℚ) ∧
    4 * Nat.choose (32 * Q + 10) 2 * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 * 13 * 12 < 10 ^ 43 ∧
    (4 : ℝ) * (Nat.choose (32 * Q + 10) 2 : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
      Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < (10 : ℝ) ^ 43 := by
  intro Q
  have h1 : (495 : ℚ) / 1000 * (2 ^ 20 : ℚ) ≥ 4 * (Q : ℚ) := by norm_num [Q]
  have h2 : ((27 : ℚ) / 10) ^ 3 > 9 := by norm_num
  have h3 : ((27 : ℚ) / 10) ^ 13 > 18 * (Q : ℚ) := by norm_num [Q]
  have h4 : ((27 : ℚ) / 10) ^ 12 > 6 * (Q : ℚ) := by norm_num [Q]
  have hC_eq := Nat.choose_two_right (32 * Q + 10)
  have h5 : 4 * Nat.choose (32 * Q + 10) 2 * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 * 13 * 12 < 10 ^ 43 := by
    rw [hC_eq]; norm_num [Q]
  have hlog9 : Real.log 9 < 3 :=
    real_log_lt_of_base_27_10 (by norm_num) (by norm_num)
  have hlog1 : Real.log (18 * (Q : ℝ)) < 13 :=
    real_log_lt_of_base_27_10 (by positivity) (by norm_num [Q])
  have hlog2 : Real.log (2 * (Q : ℝ) * Real.log 9) < 12 := by
    have hlog9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have hQpos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]
    have harg_lt : 2 * (Q : ℝ) * Real.log 9 < 6 * (Q : ℝ) := by
      have h1'' := mul_lt_mul_of_pos_left hlog9 (by positivity : (0 : ℝ) < 2 * (Q : ℝ))
      linarith
    have h1' : Real.log (2 * (Q : ℝ) * Real.log 9) < Real.log (6 * (Q : ℝ)) :=
      Real.log_lt_log (by positivity) harg_lt
    have h2' : Real.log (6 * (Q : ℝ)) < 12 :=
      real_log_lt_of_base_27_10 (by positivity) (by norm_num [Q])
    linarith
  have hlog1_pos : 0 < Real.log (18 * (Q : ℝ)) := Real.log_pos (by norm_num [Q])
  have hlog2_pos : 0 < Real.log (2 * (Q : ℝ) * Real.log 9) := by
    apply Real.log_pos
    have hlog9_gt1 : 1 < Real.log 9 := by
      have h9 : Real.exp 1 < 9 := by linarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr h9
    have hQge : (1 : ℝ) ≤ (Q : ℝ) := by norm_num [Q]
    calc (1 : ℝ) < 2 * 1 * 1 := by norm_num
      _ ≤ 2 * (Q : ℝ) * Real.log 9 := by
        have hmul1 : (2 : ℝ) * 1 ≤ 2 * (Q : ℝ) := by linarith
        exact mul_le_mul hmul1 hlog9_gt1.le (by norm_num) (by linarith)
  have hreal :
      (4 : ℝ) * (Nat.choose (32 * Q + 10) 2 : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
        Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < (10 : ℝ) ^ 43 := by
    have hC_pos : 0 < Nat.choose (32 * Q + 10) 2 := by rw [hC_eq]; norm_num [Q]
    generalize Nat.choose (32 * Q + 10) 2 = C at h5 hC_pos ⊢
    have h5r : ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) * (13 * 12 : ℝ) <
        (10 : ℝ) ^ 43 := by
      have h5' : (4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3) * (13 * 12) < 10 ^ 43 := by
        simpa [mul_assoc] using h5
      exact_mod_cast h5'
    have hQpos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]
    have hcoeff_pos : (0 : ℝ) < ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) := by
      have : 0 < 4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 := by
        have : 0 < Q := by norm_num [Q]
        positivity
      exact_mod_cast this
    have hprod_lt : Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) < 13 * 12 :=
      mul_lt_mul'' hlog1 hlog2 hlog1_pos.le hlog2_pos.le
    have hcast_lhs :
        (4 : ℝ) * (C : ℝ) * 10 ^ 9 * 2 ^ 18 * (2 * (Q : ℝ)) ^ 3 *
            Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9) =
          ((4 * C * 10 ^ 9 * 2 ^ 18 * (2 * Q) ^ 3 : ℕ) : ℝ) *
            (Real.log (18 * (Q : ℝ)) * Real.log (2 * (Q : ℝ) * Real.log 9)) := by
      push_cast; ring
    rw [hcast_lhs]
    exact lt_trans (mul_lt_mul_of_pos_left hprod_lt hcoeff_pos) h5r
  exact ⟨h1, h2, h3, h4, h5, hreal⟩

/-! ## 5. Prefactor Absorption (`k ≥ 2^40`) & Cumulative Band-Slack Arithmetic -/

/-- For every `k ≥ 2^40`, `65 + 3 * log_2(k + 1) < 4 * 10^{-9} * k` (`explicit-shell-count.md`),
absorbing the polynomial slice prefactor `2^65 * (k + 1)^3` inside the `4 * 10^{-9}` margin
below `0.94476` (and the `10^{-4}` margin below `0.945`). -/
theorem prefactor_absorption_ge_two_pow_40 {k : ℕ} (hk : 2 ^ 40 ≤ k) :
    65 + 3 * Real.logb 2 ((k : ℝ) + 1) < (4 / 10 ^ 9 : ℝ) * (k : ℝ) := by
  have hk_r : (2 ^ 40 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlog2_ge : (1 : ℝ) / 2 < Real.log 2 := by
    have := real_log_two_bounds.1; linarith
  have hratio : 1 ≤ ((k : ℝ) + 1) / (2 ^ 40 : ℝ) := by
    rw [one_le_div (by positivity)]; linarith
  have hlog_step : Real.log (((k : ℝ) + 1) / (2 ^ 40 : ℝ)) ≤ ((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hlogb_eq : Real.logb 2 ((k : ℝ) + 1) =
      40 + Real.log (((k : ℝ) + 1) / (2 ^ 40 : ℝ)) / Real.log 2 := by
    unfold Real.logb
    rw [Real.log_div hk1_pos.ne' (by positivity), Real.log_pow, sub_div]
    have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [mul_div_cancel_right₀ _ hlog2ne]
    ring
  have hlogb_le : Real.logb 2 ((k : ℝ) + 1) ≤ 40 + 2 * (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) := by
    rw [hlogb_eq]
    have h1 : Real.log (((k : ℝ) + 1) / (2 ^ 40 : ℝ)) / Real.log 2 ≤
        (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog_step (by linarith)
    have h2 : (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) / Real.log 2 ≤
        (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) / (1 / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog2_ge.le
    linarith [show (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) / (1 / 2) =
        2 * (((k : ℝ) + 1) / (2 ^ 40 : ℝ) - 1) by ring]
  linarith [hk_r, hlogb_le]

/-- Exact band-slack inequalities for `cumulative_count_outside_bands` (`exceptional-scale-count.md`):
`3.041 * 0.94995558 < 3.06 * 0.94476` and `3.041 * 0.94995558 < 3.06 * 0.945`,
and both `0.94476` and `0.945` beat Lagarias's `H_2(log_3 2) > 0.949955` by `> 0.00495`. -/
theorem cumulative_band_slack_and_lagarias_gain :
    ((3041 : ℝ) / 1000) * (94995558 / 10 ^ 8) < ((306 : ℝ) / 100) * (94476 / 10 ^ 5) ∧
    ((3041 : ℝ) / 1000) * (94995558 / 10 ^ 8) < ((306 : ℝ) / 100) * (945 / 10 ^ 3) ∧
    (945 / 10 ^ 3 : ℝ) + (4955 / 10 ^ 6 : ℝ) < binEntropy (Real.log 2 / Real.log 3) ∧
    (94476 / 10 ^ 5 : ℝ) + (5195 / 10 ^ 6 : ℝ) < binEntropy (Real.log 2 / Real.log 3) := by
  have hL := lagarias_entropy_bounds.1
  refine ⟨by norm_num, by norm_num, by linarith, by linarith⟩

end CollatzTwoWindow
