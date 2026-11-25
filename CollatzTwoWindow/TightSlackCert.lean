module

public import CollatzTwoWindow.Certificates
public import CollatzTwoWindow.WideSlackCert
public import CollatzTwoWindow.TightSlackCertData

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pure-Kernel Verification of the Tight-Slack (`σ = 10^{-7}`, Exponent `0.94476`) BSP Cover

Closes the first trust-boundary gap documented in `README.md` by certifying the sharp
tight-slack `0.05524` (`< 944759996 / 10^9 < 0.94476`, preserving `> 4 * 10^{-9}` headroom
for `prefactor_absorption_ge_two_pow_40`) binary space partition cover unconditionally in
the Lean 4 kernel (ZERO `sorry`, ZERO `native_decide`, ZERO `set_option`):

- `atanh7_real_bounds`, `neg_logb2_nat_bounds_7`, `neg_logb2_ge_of_nat_7`,
  `neg_logb2_le_of_nat_7`: 7-term `atanh` calculus log enclosures (`< 2 * 10^{-8}` width).
- `tightLogTable1024_sound`: pure-`Nat` verification of all `303` active entries of
  `tightLogTable1024` enclosing `-Real.logb 2 (k / 1024)` at scale `10^7`.
- `tightSlackBSP_ok` & `tight_slack_005524_uniform_bound`: pure-kernel verification of all
  `401` BSP leaves (`× 8` corners), proving that for EVERY `(δ, d_r) ∈ [-10^{-7}, 0.012] × [-10^{-7}, 1]`
  at `p = Real.log 2 / Real.log 3`, there exist valid tilts in `[1/1024, 1023/1024]`
  (`xi ∈ [1/65536, 65535/65536]`, `w₁ + w₀ ≤ 1`, `1/2 ≤ z₂`) certifying
  `min(U, max((N + M_2)/2, (F + M_2)/2)) < 944759996 / 10^9 < 94476 / 10^5`.
- `wide_slack_0055_uniform_bound_with_floor`: lifts `wideSlackBSP_ok` to expose the
  `[1/512, 511/512]` tilt floor needed by the slice-to-shell assembly in `BeyondBaseline.lean`.
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Exact Real-Valued Tight-Slack Slice Exponents (`σ = 10^{-7}`) -/

noncomputable def tightRho (δ : ℝ) : ℝ :=
  492 / 1000 + δ + 4 / 10 ^ 7

noncomputable def tightLen (δ : ℝ) : ℝ :=
  1 - tightRho δ

noncomputable def tightPref (δ d_r p : ℝ) : ℝ :=
  p * (tightRho δ + d_r)

noncomputable def tightSuf (δ d_r p : ℝ) : ℝ :=
  p * (1 + δ) - tightPref δ d_r p

noncomputable def tightDirect (δ d_r p x y : ℝ) : ℝ :=
  crossEntropy (tightRho δ) (tightPref δ d_r p) x +
  crossEntropy (tightLen δ) (tightSuf δ d_r p) y

noncomputable def tightNear (δ d_r p x y xi w₁ w₀ : ℝ) : ℝ :=
  tightDirect δ d_r p x y +
  crossEntropy (tightSuf δ d_r p) (xi * tightLen δ / 2) w₁ +
  crossEntropy (tightLen δ - tightSuf δ d_r p) (xi * tightLen δ / 2) w₀ +
  max 0 (tightRho δ + d_r - 508 / 1000) + 1 / 10 ^ 7

noncomputable def tightFar (δ d_r p x xi q : ℝ) : ℝ :=
  2 * crossEntropy (tightRho δ) (tightPref δ d_r p) x +
  xi * tightLen δ +
  crossEntropy (tightLen δ - xi * tightLen δ) (tightSuf δ d_r p - xi * tightLen δ / 2) q

noncomputable def tightMenu (δ p z₂ : ℝ) : ℝ :=
  crossEntropy (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂

/-! ## 2. Pure-`Nat` 7-Term `atanh` Enclosure and `tightLogTable1024` Verification -/

/-- Closed-form 7-term `atanh` numerator over `45045 * w^13` (`lcm(1,3,5,7,9,11,13) = 45045`). -/
def atanh7LowerNum (u w : ℕ) : ℕ :=
  2 * (45045 * u * w ^ 12 + 15015 * u ^ 3 * w ^ 10 + 9009 * u ^ 5 * w ^ 8 +
    6435 * u ^ 7 * w ^ 6 + 5005 * u ^ 9 * w ^ 4 + 4095 * u ^ 11 * w ^ 2 +
    3465 * u ^ 13)

def atanh7Den (w : ℕ) : ℕ :=
  45045 * w ^ 13

/-- Exact integer numerator for the 7-term upper bound `atanhPartial 7 + atanhTail 7`
over common denominator `45045 * w^13 * (w^2 - u^2)` (since `45045 = 15 * 3003`). -/
def atanh7UpperNum (u w : ℕ) : ℕ :=
  (w * w - u * u) * atanh7LowerNum u w + 6006 * u ^ 15

def atanh7UpperDen (u w : ℕ) : ℕ :=
  45045 * w ^ 13 * (w * w - u * u)

theorem atanh7_real_bounds {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    (atanh7LowerNum (a - b) (a + b) : ℝ) / (atanh7Den (a + b) : ℝ) ≤
      Real.log ((a : ℝ) / (b : ℝ)) ∧
    Real.log ((a : ℝ) / (b : ℝ)) ≤
      (atanh7UpperNum (a - b) (a + b) : ℝ) / (atanh7UpperDen (a - b) (a + b) : ℝ) := by
  have hbr : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hvr : (1 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
    rw [one_le_div hbr]; exact_mod_cast hba
  have hbnd := real_log_atanh_bounds 7 hvr
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
      atanhPartial 7 ((u : ℝ) / (w : ℝ)) =
        (atanh7LowerNum u w : ℝ) / (atanh7Den w : ℝ) := by
    unfold atanhPartial atanh7LowerNum atanh7Den
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    push_cast
    field_simp [hw_pos.ne']
    ring
  have hup :
      atanhPartial 7 ((u : ℝ) / (w : ℝ)) + atanhTail 7 ((u : ℝ) / (w : ℝ)) =
        (atanh7UpperNum u w : ℝ) / (atanh7UpperDen u w : ℝ) := by
    rw [hpart]
    unfold atanhTail atanh7UpperNum atanh7UpperDen atanh7Den
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

theorem neg_logb2_nat_bounds_7 {k d sh : ℕ} (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) :
    let a := d
    let b := k * 2 ^ sh
    (sh : ℝ) + ((atanh7LowerNum (a - b) (a + b) : ℝ) / (atanh7Den (a + b) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) ≤ -Real.logb 2 ((k : ℝ) / (d : ℝ)) ∧
    -Real.logb 2 ((k : ℝ) / (d : ℝ)) ≤
      (sh : ℝ) + ((atanh7UpperNum (a - b) (a + b) : ℝ) / (atanh7UpperDen (a - b) (a + b) : ℝ)) /
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
  have hatanh := atanh7_real_bounds hb_pos hred
  have hlog2 := real_log_two_bounds
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogv_nonneg : 0 ≤ Real.log ((a : ℝ) / (b : ℝ)) := Real.log_nonneg hab_ge1
  constructor
  · have h1 : ((atanh7LowerNum (a - b) (a + b) : ℝ) / (atanh7Den (a + b) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) ≤ Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 := by
      calc _ ≤ Real.log ((a : ℝ) / (b : ℝ)) / ((693147181 : ℝ) / 10 ^ 9) :=
            div_le_div_of_nonneg_right hatanh.1 (by norm_num)
        _ ≤ Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 :=
            div_le_div_of_nonneg_left hlogv_nonneg hlog2_pos hlog2.2.le
    linarith
  · have h2 : Real.log ((a : ℝ) / (b : ℝ)) / Real.log 2 ≤
        ((atanh7UpperNum (a - b) (a + b) : ℝ) / (atanh7UpperDen (a - b) (a + b) : ℝ)) /
        ((693147180 : ℝ) / 10 ^ 9) := by
      calc _ ≤ ((atanh7UpperNum (a - b) (a + b) : ℝ) / (atanh7UpperDen (a - b) (a + b) : ℝ)) /
              Real.log 2 := div_le_div_of_nonneg_right hatanh.2 hlog2_pos.le
        _ ≤ _ := div_le_div_of_nonneg_left (hlogv_nonneg.trans hatanh.2) (by norm_num) hlog2.1.le
    linarith

theorem neg_logb2_ge_of_nat_7 {k d sh loNum scale : ℕ}
    (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) (hscale : 0 < scale) (hsh : sh * scale ≤ loNum)
    (hnat : (loNum - sh * scale) * atanh7Den (d + k * 2 ^ sh) * 693147181 ≤
      atanh7LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) * (scale * 10 ^ 9)) :
    (loNum : ℝ) / (scale : ℝ) ≤ -Real.logb 2 ((k : ℝ) / (d : ℝ)) := by
  have hb := (neg_logb2_nat_bounds_7 hk hred).1
  have hsc_pos : (0 : ℝ) < (scale : ℝ) := Nat.cast_pos.mpr hscale
  have hden_pos : (0 : ℝ) < (atanh7Den (d + k * 2 ^ sh) : ℝ) := by
    unfold atanh7Den
    have : 0 < d + k * 2 ^ sh := by have := Nat.mul_pos hk (by positivity : 0 < 2 ^ sh); omega
    positivity
  have hsub_cast : ((loNum - sh * scale : ℕ) : ℝ) = (loNum : ℝ) - (sh : ℝ) * (scale : ℝ) := by
    rw [Nat.cast_sub hsh]; push_cast; rfl
  have hnat_r : ((loNum : ℝ) - (sh : ℝ) * (scale : ℝ)) * (atanh7Den (d + k * 2 ^ sh) : ℝ) *
      693147181 ≤ (atanh7LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * ((scale : ℝ) * 10 ^ 9) := by
    rw [← hsub_cast]; exact_mod_cast hnat
  have hdiv : (loNum : ℝ) / (scale : ℝ) - (sh : ℝ) ≤
      ((atanh7LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) / (atanh7Den (d + k * 2 ^ sh) : ℝ)) /
        ((693147181 : ℝ) / 10 ^ 9) := by
    have h1 : (loNum : ℝ) / (scale : ℝ) - (sh : ℝ) =
        ((loNum : ℝ) - (sh : ℝ) * (scale : ℝ)) / (scale : ℝ) := by field_simp [hsc_pos.ne']
    have h2 : ((atanh7LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh7Den (d + k * 2 ^ sh) : ℝ)) / ((693147181 : ℝ) / 10 ^ 9) =
        ((atanh7LowerNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 10 ^ 9) /
        ((atanh7Den (d + k * 2 ^ sh) : ℝ) * 693147181) := by field_simp [hden_pos.ne']
    rw [h1, h2, div_le_div_iff₀ hsc_pos (by positivity)]
    linarith
  linarith

theorem neg_logb2_le_of_nat_7 {k d sh hiNum scale : ℕ}
    (hk : 0 < k) (hred : k * 2 ^ sh ≤ d) (hscale : 0 < scale) (hsh : sh * scale ≤ hiNum)
    (hnat : atanh7UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) * (scale * 10 ^ 9) ≤
      (hiNum - sh * scale) * atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) * 693147180) :
    -Real.logb 2 ((k : ℝ) / (d : ℝ)) ≤ (hiNum : ℝ) / (scale : ℝ) := by
  have hb := (neg_logb2_nat_bounds_7 hk hred).2
  have hsc_pos : (0 : ℝ) < (scale : ℝ) := Nat.cast_pos.mpr hscale
  have hb_pos : 0 < k * 2 ^ sh := Nat.mul_pos hk (by positivity)
  have hden_pos : (0 : ℝ) < (atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) := by
    unfold atanh7UpperDen
    have h1 : 0 < d + k * 2 ^ sh := by omega
    have h2 : (d - k * 2 ^ sh) * (d - k * 2 ^ sh) < (d + k * 2 ^ sh) * (d + k * 2 ^ sh) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    have h3 : 0 < (d + k * 2 ^ sh) * (d + k * 2 ^ sh) - (d - k * 2 ^ sh) * (d - k * 2 ^ sh) :=
      Nat.sub_pos_of_lt h2
    positivity
  have hsub_cast : ((hiNum - sh * scale : ℕ) : ℝ) = (hiNum : ℝ) - (sh : ℝ) * (scale : ℝ) := by
    rw [Nat.cast_sub hsh]; push_cast; rfl
  have hnat_r : (atanh7UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * ((scale : ℝ) * 10 ^ 9) ≤
      ((hiNum : ℝ) - (sh : ℝ) * (scale : ℝ)) *
        (atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 693147180 := by
    rw [← hsub_cast]; exact_mod_cast hnat
  have hdiv : ((atanh7UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ)) / ((693147180 : ℝ) / 10 ^ 9) ≤
      (hiNum : ℝ) / (scale : ℝ) - (sh : ℝ) := by
    have h1 : (hiNum : ℝ) / (scale : ℝ) - (sh : ℝ) =
        ((hiNum : ℝ) - (sh : ℝ) * (scale : ℝ)) / (scale : ℝ) := by field_simp [hsc_pos.ne']
    have h2 : ((atanh7UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) /
        (atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ)) / ((693147180 : ℝ) / 10 ^ 9) =
        ((atanh7UpperNum (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 10 ^ 9) /
        ((atanh7UpperDen (d - k * 2 ^ sh) (d + k * 2 ^ sh) : ℝ) * 693147180) := by
      field_simp [hden_pos.ne']
    rw [h1, h2, div_le_div_iff₀ (by positivity) hsc_pos]
    linarith
  linarith

def tightLogLo (k : ℕ) : ℕ :=
  (tightLogTable1024.getD k (0, 0, 0)).2.1

def tightLogHi (k : ℕ) : ℕ :=
  (tightLogTable1024.getD k (0, 0, 0)).2.2

def checkTightLogEntry1024 (k : ℕ) : Bool :=
  let lo := tightLogLo k
  if lo == 0 then true
  else
    let sh := (tightLogTable1024.getD k (0, 0, 0)).1
    let hi := tightLogHi k
    let a := 1024
    let b := k * 2 ^ sh
    decide (0 < k ∧ b ≤ a ∧ sh * 10 ^ 7 ≤ lo ∧ sh * 10 ^ 7 ≤ hi ∧
      (lo - sh * 10 ^ 7) * atanh7Den (a + b) * 693147181 ≤
        atanh7LowerNum (a - b) (a + b) * 10 ^ 16 ∧
      atanh7UpperNum (a - b) (a + b) * 10 ^ 16 ≤
        (hi - sh * 10 ^ 7) * atanh7UpperDen (a - b) (a + b) * 693147180)

def checkTightLogRange (offset : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => checkTightLogEntry1024 (offset + n + 1) && checkTightLogRange offset n

theorem checkTightLogTable1024_lo_ok : checkTightLogRange 0 512 = true := by
  decide +kernel

theorem checkTightLogTable1024_hi_ok : checkTightLogRange 512 511 = true := by
  decide +kernel

private lemma checkTightLogRange_imp (offset : ℕ) :
    ∀ n : ℕ, checkTightLogRange offset n = true →
      ∀ k : ℕ, offset + 1 ≤ k → k ≤ offset + n → checkTightLogEntry1024 k = true
  | 0, _, k, hk1, hk0 => by omega
  | n + 1, h, k, hk1, hkn => by
      simp only [checkTightLogRange, Bool.and_eq_true] at h
      by_cases hkeq : k = offset + n + 1
      · subst hkeq; exact h.1
      · exact checkTightLogRange_imp offset n h.2 k hk1 (by omega)

theorem tightLogTable1024_sound {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 1024) (hpos : 0 < tightLogLo k) :
    (tightLogLo k : ℝ) / 10 ^ 7 ≤ -Real.logb 2 ((k : ℝ) / 1024) ∧
    -Real.logb 2 ((k : ℝ) / 1024) ≤ (tightLogHi k : ℝ) / 10 ^ 7 := by
  have hentry : checkTightLogEntry1024 k = true := by
    by_cases hle : k ≤ 512
    · exact checkTightLogRange_imp 0 512 checkTightLogTable1024_lo_ok k (by omega) (by omega)
    · exact checkTightLogRange_imp 512 511 checkTightLogTable1024_hi_ok k (by omega) (by omega)
  unfold checkTightLogEntry1024 at hentry
  have hne : (tightLogLo k == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
  dsimp only at hentry
  rw [hne] at hentry
  simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hentry
  obtain ⟨hkpos, hba, hshlo, hshhi, hlo_nat, hhi_nat⟩ := hentry
  have hlo := neg_logb2_ge_of_nat_7 hkpos hba (by decide : 0 < 10 ^ 7) hshlo
    (by simpa [show (10 ^ 7 : ℕ) * 10 ^ 9 = 10 ^ 16 by decide] using hlo_nat)
  have hhi := neg_logb2_le_of_nat_7 hkpos hba (by decide : 0 < 10 ^ 7) hshhi
    (by simpa [show (10 ^ 7 : ℕ) * 10 ^ 9 = 10 ^ 16 by decide] using hhi_nat)
  have h10 : ((10 ^ 7 : ℕ) : ℝ) = (10 : ℝ) ^ 7 := by norm_num
  have h1024 : ((1024 : ℕ) : ℝ) = (1024 : ℝ) := by norm_num
  rw [h10, h1024] at hlo hhi
  exact ⟨hlo, hhi⟩

/-! ## 3. Coordinatewise-Convex Upper Envelopes for Tight Slack -/

noncomputable def tightCostEnv (c : ℝ) (k : ℕ) : ℝ :=
  max (c * ((tightLogLo k : ℝ) / 10 ^ 7)) (c * ((tightLogHi k : ℝ) / 10 ^ 7))

noncomputable def tightCrossEnv (a j : ℝ) (k : ℕ) : ℝ :=
  tightCostEnv j k + tightCostEnv (a - j) (1024 - k)

noncomputable def tightDirectEnv (δ d_r p : ℝ) (xk yk : ℕ) : ℝ :=
  tightCrossEnv (tightRho δ) (tightPref δ d_r p) xk +
  tightCrossEnv (tightLen δ) (tightSuf δ d_r p) yk

noncomputable def tightNearMenuEnv (δ d_r p : ℝ) (xk yk xik w1k w0k z2k : ℕ) : ℝ :=
  tightDirectEnv δ d_r p xk yk +
  tightCrossEnv (tightSuf δ d_r p) ((xik : ℝ) / 65536 * tightLen δ / 2) w1k +
  tightCrossEnv (tightLen δ - tightSuf δ d_r p) ((xik : ℝ) / 65536 * tightLen δ / 2) w0k +
  max 0 (tightRho δ + d_r - 508 / 1000) + 1 / 10 ^ 7 +
  tightCrossEnv (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z2k

noncomputable def tightFarMenuEnv (δ d_r p : ℝ) (xk xik qk z2k : ℕ) : ℝ :=
  2 * tightCrossEnv (tightRho δ) (tightPref δ d_r p) xk +
  (xik : ℝ) / 65536 * tightLen δ +
  tightCrossEnv (tightLen δ - (xik : ℝ) / 65536 * tightLen δ)
    (tightSuf δ d_r p - (xik : ℝ) / 65536 * tightLen δ / 2) qk +
  tightCrossEnv (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z2k

private lemma crossEntropy_le_tightCrossEnv (a j : ℝ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k < 1024)
    (hpos1 : 0 < tightLogLo k) (hpos2 : 0 < tightLogLo (1024 - k)) :
    crossEntropy a j ((k : ℝ) / 1024) ≤ tightCrossEnv a j k := by
  have hk := tightLogTable1024_sound hk1 hk2 hpos1
  have hkc := tightLogTable1024_sound (k := 1024 - k) (by omega) (by omega) hpos2
  have hcomp : 1 - (k : ℝ) / 1024 = ((1024 - k : ℕ) : ℝ) / 1024 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : j * (-Real.logb 2 ((k : ℝ) / 1024)) ≤ tightCostEnv j k := by
    unfold tightCostEnv
    by_cases hj : 0 ≤ j
    · exact le_trans (mul_le_mul_of_nonneg_left hk.2 hj) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hk.1 (le_of_not_ge hj)) (le_max_left _ _)
  have h2 : (a - j) * (-Real.logb 2 (1 - (k : ℝ) / 1024)) ≤ tightCostEnv (a - j) (1024 - k) := by
    rw [hcomp]
    unfold tightCostEnv
    by_cases hj : 0 ≤ a - j
    · exact le_trans (mul_le_mul_of_nonneg_left hkc.2 hj) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hkc.1 (le_of_not_ge hj)) (le_max_left _ _)
  unfold crossEntropy tightCrossEnv
  linarith

private lemma isConvexR_const' (c : ℝ) : IsConvexR (fun _ => c) := by
  intro a b t _ _; linarith

private lemma isConvexR_affine' (m c : ℝ) : IsConvexR (fun x => m * x + c) := by
  intro a b t _ _; linarith

private lemma isConvexR_add' {φ ψ : ℝ → ℝ} (h1 : IsConvexR φ) (h2 : IsConvexR ψ) :
    IsConvexR (fun x => φ x + ψ x) := by
  intro a b t ht0 ht1
  linarith [h1 a b t ht0 ht1, h2 a b t ht0 ht1]

private lemma isConvexR_const_mul' {c : ℝ} (hc : 0 ≤ c) {φ : ℝ → ℝ} (h : IsConvexR φ) :
    IsConvexR (fun x => c * φ x) := by
  intro a b t ht0 ht1
  have := mul_le_mul_of_nonneg_left (h a b t ht0 ht1) hc
  linarith

private lemma isConvexR_max' {φ ψ : ℝ → ℝ} (h1 : IsConvexR φ) (h2 : IsConvexR ψ) :
    IsConvexR (fun x => max (φ x) (ψ x)) := by
  intro a b t ht0 ht1
  apply max_le
  · calc φ ((1 - t) * a + t * b) ≤ (1 - t) * φ a + t * φ b := h1 a b t ht0 ht1
      _ ≤ (1 - t) * max (φ a) (ψ a) + t * max (φ b) (ψ b) := by
        have := mul_le_mul_of_nonneg_left (le_max_left (φ a) (ψ a)) (by linarith : 0 ≤ 1 - t)
        have := mul_le_mul_of_nonneg_left (le_max_left (φ b) (ψ b)) ht0
        linarith
  · calc ψ ((1 - t) * a + t * b) ≤ (1 - t) * ψ a + t * ψ b := h2 a b t ht0 ht1
      _ ≤ (1 - t) * max (φ a) (ψ a) + t * max (φ b) (ψ b) := by
        have := mul_le_mul_of_nonneg_left (le_max_right (φ a) (ψ a)) (by linarith : 0 ≤ 1 - t)
        have := mul_le_mul_of_nonneg_left (le_max_right (φ b) (ψ b)) ht0
        linarith

private lemma isConvexR_congr' {φ ψ : ℝ → ℝ} (h : IsConvexR φ) (heq : ∀ x, φ x = ψ x) :
    IsConvexR ψ := by
  intro a b t ht0 ht1
  rw [← heq, ← heq, ← heq]
  exact h a b t ht0 ht1

private lemma isConvexR_tightCostEnv_affine (m c : ℝ) (k : ℕ) :
    IsConvexR (fun x => tightCostEnv (m * x + c) k) := by
  unfold tightCostEnv
  apply isConvexR_max'
  · have h := isConvexR_affine' (m * ((tightLogLo k : ℝ) / 10 ^ 7)) (c * ((tightLogLo k : ℝ) / 10 ^ 7))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith
  · have h := isConvexR_affine' (m * ((tightLogHi k : ℝ) / 10 ^ 7)) (c * ((tightLogHi k : ℝ) / 10 ^ 7))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith

private lemma isConvexR_tightCrossEnv_affine (m₁ c₁ m₂ c₂ : ℝ) (k : ℕ) :
    IsConvexR (fun x => tightCrossEnv (m₁ * x + c₁) (m₂ * x + c₂) k) := by
  unfold tightCrossEnv
  apply isConvexR_add'
  · exact isConvexR_tightCostEnv_affine m₂ c₂ k
  · have h := isConvexR_tightCostEnv_affine (m₁ - m₂) (c₁ - c₂) (1024 - k)
    intro a b t ht0 ht1
    have := h a b t ht0 ht1
    have heq : ∀ y : ℝ, (m₁ - m₂) * y + (c₁ - c₂) = m₁ * y + c₁ - (m₂ * y + c₂) := fun y => by ring
    simpa [heq] using this

private lemma tightDirectEnv_convex_d (e p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun d => tightDirectEnv d e p xk yk) := by
  unfold tightDirectEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 1 (492 / 1000 + 4 / 10 ^ 7)
        p (p * (492 / 1000 + 4 / 10 ^ 7 + e)) xk) (fun x => ?_)
    unfold tightPref tightRho; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine (-1) (1 - (492 / 1000 + 4 / 10 ^ 7))
        0 (p * (1 - (492 / 1000 + 4 / 10 ^ 7 + e))) yk) (fun x => ?_)
    unfold tightLen tightSuf tightPref tightRho; congr 1 <;> ring

private lemma tightDirectEnv_convex_e (d p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun e => tightDirectEnv d e p xk yk) := by
  unfold tightDirectEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (tightRho d) p (p * tightRho d) xk) (fun x => ?_)
    unfold tightPref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (tightLen d) (-p) (p * (1 + d) - p * tightRho d) yk) (fun x => ?_)
    unfold tightSuf tightPref; congr 1 <;> ring

private lemma tightDirectEnv_convex_p (d e : ℝ) (xk yk : ℕ) :
    IsConvexR (fun p => tightDirectEnv d e p xk yk) := by
  unfold tightDirectEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (tightRho d) (tightRho d + e) 0 xk) (fun x => ?_)
    unfold tightPref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (tightLen d) (1 + d - (tightRho d + e)) 0 yk) (fun x => ?_)
    unfold tightSuf tightPref; congr 1 <;> ring

private lemma tightNearMenuEnv_convex_d (e p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun d => tightNearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold tightNearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact tightDirectEnv_convex_d e p xk yk
          · refine isConvexR_congr'
              (isConvexR_tightCrossEnv_affine 0 (p * (1 - (492 / 1000 + 4 / 10 ^ 7 + e)))
                (-((xik : ℝ) / 65536 / 2))
                ((xik : ℝ) / 65536 * (1 - (492 / 1000 + 4 / 10 ^ 7)) / 2) w1k)
              (fun x => ?_)
            unfold tightSuf tightPref tightLen tightRho; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_tightCrossEnv_affine (-1)
              (1 - (492 / 1000 + 4 / 10 ^ 7) -
                p * (1 - (492 / 1000 + 4 / 10 ^ 7 + e)))
              (-((xik : ℝ) / 65536 / 2))
              ((xik : ℝ) / 65536 * (1 - (492 / 1000 + 4 / 10 ^ 7)) / 2) w0k)
            (fun x => ?_)
          unfold tightLen tightSuf tightPref tightRho; congr 1 <;> ring
      · apply isConvexR_max' (isConvexR_const' 0)
        refine isConvexR_congr'
          (isConvexR_affine' 1 (492 / 1000 + 4 / 10 ^ 7 + e - 508 / 1000))
          (fun x => by unfold tightRho; ring)
    · exact isConvexR_const' (1 / 10 ^ 7)
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma tightNearMenuEnv_convex_e (d p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun e => tightNearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold tightNearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact tightDirectEnv_convex_e d p xk yk
          · refine isConvexR_congr'
              (isConvexR_tightCrossEnv_affine (-p) (p * (1 + d) - p * tightRho d)
                0 ((xik : ℝ) / 65536 * tightLen d / 2) w1k) (fun x => ?_)
            unfold tightSuf tightPref; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_tightCrossEnv_affine p (tightLen d - (p * (1 + d) - p * tightRho d))
              0 ((xik : ℝ) / 65536 * tightLen d / 2) w0k) (fun x => ?_)
          unfold tightSuf tightPref; congr 1 <;> ring
      · apply isConvexR_max' (isConvexR_const' 0)
        refine isConvexR_congr' (isConvexR_affine' 1 (tightRho d - 508 / 1000)) (fun _ => by ring)
    · exact isConvexR_const' (1 / 10 ^ 7)
  · exact isConvexR_const' _

private lemma tightNearMenuEnv_convex_p (d e : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun p => tightNearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold tightNearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact tightDirectEnv_convex_p d e xk yk
          · refine isConvexR_congr'
              (isConvexR_tightCrossEnv_affine (1 + d - (tightRho d + e)) 0
                0 ((xik : ℝ) / 65536 * tightLen d / 2) w1k) (fun x => ?_)
            unfold tightSuf tightPref; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_tightCrossEnv_affine (-(1 + d - (tightRho d + e))) (tightLen d)
              0 ((xik : ℝ) / 65536 * tightLen d / 2) w0k) (fun x => ?_)
          unfold tightSuf tightPref; congr 1 <;> ring
      · exact isConvexR_const' _
    · exact isConvexR_const' (1 / 10 ^ 7)
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma tightFarMenuEnv_convex_d (e p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun d => tightFarMenuEnv d e p xk xik qk z2k) := by
  unfold tightFarMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_tightCrossEnv_affine 1 (492 / 1000 + 4 / 10 ^ 7)
            p (p * (492 / 1000 + 4 / 10 ^ 7 + e)) xk) (fun x => ?_)
        unfold tightPref tightRho; congr 1 <;> ring
      · refine isConvexR_congr'
          (isConvexR_affine' (-((xik : ℝ) / 65536))
            ((xik : ℝ) / 65536 * (1 - (492 / 1000 + 4 / 10 ^ 7))))
          (fun x => by unfold tightLen tightRho; ring)
    · refine isConvexR_congr'
        (isConvexR_tightCrossEnv_affine (-(1 - (xik : ℝ) / 65536))
          ((1 - (xik : ℝ) / 65536) * (1 - (492 / 1000 + 4 / 10 ^ 7)))
          ((xik : ℝ) / 65536 / 2)
          (p * (1 - (492 / 1000 + 4 / 10 ^ 7 + e)) -
            (xik : ℝ) / 65536 * (1 - (492 / 1000 + 4 / 10 ^ 7)) / 2) qk)
        (fun x => ?_)
      unfold tightSuf tightPref tightLen tightRho; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma tightFarMenuEnv_convex_e (d p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun e => tightFarMenuEnv d e p xk xik qk z2k) := by
  unfold tightFarMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_tightCrossEnv_affine 0 (tightRho d) p (p * tightRho d) xk) (fun x => ?_)
        unfold tightPref; congr 1 <;> ring
      · exact isConvexR_const' _
    · refine isConvexR_congr'
        (isConvexR_tightCrossEnv_affine 0 (tightLen d - (xik : ℝ) / 65536 * tightLen d)
          (-p) (p * (1 + d) - p * tightRho d - (xik : ℝ) / 65536 * tightLen d / 2) qk) (fun x => ?_)
      unfold tightSuf tightPref; congr 1 <;> ring
  · exact isConvexR_const' _

private lemma tightFarMenuEnv_convex_p (d e : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun p => tightFarMenuEnv d e p xk xik qk z2k) := by
  unfold tightFarMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_tightCrossEnv_affine 0 (tightRho d) (tightRho d + e) 0 xk) (fun x => ?_)
        unfold tightPref; congr 1 <;> ring
      · exact isConvexR_const' _
    · refine isConvexR_congr'
        (isConvexR_tightCrossEnv_affine 0 (tightLen d - (xik : ℝ) / 65536 * tightLen d)
          (1 + d - (tightRho d + e)) (-((xik : ℝ) / 65536 * tightLen d / 2)) qk) (fun x => ?_)
      unfold tightSuf tightPref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_tightCrossEnv_affine 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

/-! ## 4. Pure-`Int` Tight-Slack BSP Checker and Full Kernel Verification -/

def dCoordTight : ℤ := 10 ^ 10 * 2 ^ 16
def dTotTight : ℤ := dCoordTight * 10 ^ 8 * 2 ^ 17 * 10 ^ 7

def tightCostInt (cS : ℤ) (k : ℕ) : ℤ :=
  max (cS * (tightLogLo k : ℤ)) (cS * (tightLogHi k : ℤ))

def tightCrossInt (lenS onesS : ℤ) (k : ℕ) : ℤ :=
  tightCostInt onesS k + tightCostInt (lenS - onesS) (1024 - k)

def checkTightCornerInt (dI eI pI : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ) : Bool :=
  let rhoI : ℤ := 4920004000 * 2 ^ 16 + dI
  let lenI : ℤ := dCoordTight - rhoI
  let rhoS : ℤ := 2 ^ 17 * 10 ^ 8 * rhoI
  let lenS : ℤ := 2 ^ 17 * 10 ^ 8 * lenI
  let prefS : ℤ := 2 ^ 17 * pI * (rhoI + eI)
  let sufS : ℤ := 2 ^ 17 * pI * (dCoordTight + dI) - prefS
  let firstInt : ℤ := tightCrossInt rhoS prefS xk
  let directInt : ℤ := firstInt + tightCrossInt lenS sufS yk
  if !useColl then
    decide (10 ^ 9 * directInt < 944759996 * dTotTight)
  else
    let halfDistS : ℤ := (xik : ℤ) * 10 ^ 8 * lenI
    let distS : ℤ := 2 * halfDistS
    let betaS : ℤ := 2 ^ 17 * 10 ^ 8 * (5080000000 * 2 ^ 16)
    let menuOnesS : ℤ := 2 ^ 17 * pI * (5080000000 * 2 ^ 16 - dI - 1508 * 2 ^ 16)
    let recovInt : ℤ :=
      max 0 (rhoI + eI - 5080000000 * 2 ^ 16) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) +
      (10 ^ 3 * 2 ^ 16) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7)
    let nearInt : ℤ :=
      directInt + tightCrossInt sufS halfDistS w1k + tightCrossInt (lenS - sufS) halfDistS w0k + recovInt
    let farInt : ℤ :=
      2 * firstInt + distS * 10 ^ 7 + tightCrossInt (lenS - distS) (sufS - halfDistS) qk
    let menuInt : ℤ := tightCrossInt betaS menuOnesS z2k
    decide (10 ^ 9 * (nearInt + menuInt) < 2 * 944759996 * dTotTight ∧
      10 ^ 9 * (farInt + menuInt) < 2 * 944759996 * dTotTight)

def checkTightLeafInt (d0 d1 e0 e1 : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ) : Bool :=
  decide (1 ≤ xk ∧ xk < 1024 ∧ 1 ≤ yk ∧ yk < 1024 ∧ 1 ≤ xik ∧ xik < 65536 ∧
    1 ≤ w1k ∧ w1k < 1024 ∧ 1 ≤ w0k ∧ w0k < 1024 ∧ w1k + w0k ≤ 1024 ∧
    1 ≤ qk ∧ qk < 1024 ∧ 512 ≤ z2k ∧ z2k < 1024 ∧
    0 < tightLogLo xk ∧ 0 < tightLogLo (1024 - xk) ∧
    0 < tightLogLo yk ∧ 0 < tightLogLo (1024 - yk) ∧
    0 < tightLogLo w1k ∧ 0 < tightLogLo (1024 - w1k) ∧
    0 < tightLogLo w0k ∧ 0 < tightLogLo (1024 - w0k) ∧
    0 < tightLogLo qk ∧ 0 < tightLogLo (1024 - qk) ∧
    0 < tightLogLo z2k ∧ 0 < tightLogLo (1024 - z2k)) &&
  checkTightCornerInt d0 e0 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d0 e0 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d0 e1 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d0 e1 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d1 e0 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d1 e0 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d1 e1 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkTightCornerInt d1 e1 63092976 useColl xk yk xik w1k w0k qk z2k

def checkTightBSP (d0 d1 e0 e1 : ℤ) : BSPTree → Bool
  | .leaf useColl xk yk xik w1k w0k qk z2k =>
      checkTightLeafInt d0 d1 e0 e1 useColl xk yk xik w1k w0k qk z2k
  | .splitD l r =>
      let mid := (d0 + d1) / 2
      decide (2 * mid = d0 + d1) && checkTightBSP d0 mid e0 e1 l && checkTightBSP mid d1 e0 e1 r
  | .splitE l r =>
      let mid := (e0 + e1) / 2
      decide (2 * mid = e0 + e1) && checkTightBSP d0 d1 e0 mid l && checkTightBSP d0 d1 mid e1 r

theorem tightSlackBSP_sub0_ok :
    checkTightBSP 5898223616000 7864320000000 (-65536000) 2559934720000 tightSlackBSP_0 = true := by
  decide +kernel

theorem tightSlackBSP_sub1_ok :
    checkTightBSP 5898223616000 7864320000000 2559934720000 5119934976000 tightSlackBSP_1 = true := by
  decide +kernel

theorem tightSlackBSP_sub2_ok :
    checkTightBSP 6389747712000 6881271808000 5119934976000 5759935040000 tightSlackBSP_2 = true := by
  decide +kernel

/-- **Pure-Kernel Verification of All 401 Tight-Slack BSP Rectangles (`decide +kernel`, ZERO `native_decide`):** -/
theorem tightSlackBSP_ok :
    checkTightBSP (-10 ^ 3 * 2 ^ 16) (12 * 10 ^ 7 * 2 ^ 16)
      (-10 ^ 3 * 2 ^ 16) (10 ^ 10 * 2 ^ 16) tightSlackBSP = true := by
  unfold tightSlackBSP
  simp only [checkTightBSP,
    show (-10 ^ 3 * 2 ^ 16 : ℤ) = -65536000 by decide,
    show (12 * 10 ^ 7 * 2 ^ 16 : ℤ) = 7864320000000 by decide,
    show (10 ^ 10 * 2 ^ 16 : ℤ) = 655360000000000 by decide]
  norm_num only
  rw [tightSlackBSP_sub0_ok, tightSlackBSP_sub1_ok, tightSlackBSP_sub2_ok]
  decide +kernel

private lemma max_div_pos' {a b c : ℝ} (hc : 0 < c) : max a b / c = max (a / c) (b / c) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hc.le)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (div_le_div_of_nonneg_right h' hc.le)]

private lemma tightCostInt_cast (cS : ℤ) (k : ℕ) :
    (tightCostInt cS k : ℝ) / (dTotTight : ℝ) =
      tightCostEnv ((cS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17)) k := by
  unfold tightCostInt tightCostEnv
  have hd_pos : (0 : ℝ) < (dTotTight : ℝ) := by unfold dTotTight dCoordTight; positivity
  have hcast : ((max (cS * (tightLogLo k : ℤ)) (cS * (tightLogHi k : ℤ)) : ℤ) : ℝ) =
      max ((cS : ℝ) * (tightLogLo k : ℝ)) ((cS : ℝ) * (tightLogHi k : ℝ)) := by push_cast; rfl
  rw [hcast, max_div_pos' hd_pos]
  unfold dTotTight
  push_cast
  congr 1 <;> ring

private lemma tightCrossInt_cast (lenS onesS : ℤ) (k : ℕ) :
    (tightCrossInt lenS onesS k : ℝ) / (dTotTight : ℝ) =
      tightCrossEnv ((lenS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17))
        ((onesS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17)) k := by
  unfold tightCrossInt tightCrossEnv
  push_cast
  rw [add_div, tightCostInt_cast, tightCostInt_cast]
  congr 2
  push_cast
  ring

private lemma checkTightCornerInt_sound (dI eI pI : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ)
    (hok : checkTightCornerInt dI eI pI useColl xk yk xik w1k w0k qk z2k = true) :
    let d : ℝ := (dI : ℝ) / (dCoordTight : ℝ)
    let e : ℝ := (eI : ℝ) / (dCoordTight : ℝ)
    let p : ℝ := (pI : ℝ) / 10 ^ 8
    (useColl = false → tightDirectEnv d e p xk yk < 944759996 / 10 ^ 9) ∧
    (useColl = true →
      tightNearMenuEnv d e p xk yk xik w1k w0k z2k < 2 * (944759996 / 10 ^ 9) ∧
      tightFarMenuEnv d e p xk xik qk z2k < 2 * (944759996 / 10 ^ 9)) := by
  intro d e p
  have hdTot_pos : (0 : ℝ) < (dTotTight : ℝ) := by unfold dTotTight dCoordTight; positivity
  set rhoI : ℤ := 4920004000 * 2 ^ 16 + dI
  set lenI : ℤ := dCoordTight - rhoI
  set rhoS : ℤ := 2 ^ 17 * 10 ^ 8 * rhoI
  set lenS : ℤ := 2 ^ 17 * 10 ^ 8 * lenI
  set prefS : ℤ := 2 ^ 17 * pI * (rhoI + eI)
  set sufS : ℤ := 2 ^ 17 * pI * (dCoordTight + dI) - prefS
  have hrho : (rhoS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) = tightRho d := by
    dsimp [rhoS, rhoI, d]; unfold tightRho dCoordTight; push_cast; ring
  have hlen : (lenS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) = tightLen d := by
    dsimp [lenS, lenI, rhoI, d]; unfold tightLen tightRho dCoordTight; push_cast; ring
  have hpref : (prefS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) = tightPref d e p := by
    dsimp [prefS, rhoI, d, e, p]; unfold tightPref tightRho dCoordTight; push_cast; ring
  have hsuf : (sufS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) = tightSuf d e p := by
    dsimp [sufS, prefS, rhoI, d, e, p]; unfold tightSuf tightPref tightRho dCoordTight; push_cast; ring
  have hdir_eq : ((tightCrossInt rhoS prefS xk + tightCrossInt lenS sufS yk : ℤ) : ℝ) / (dTotTight : ℝ) =
      tightDirectEnv d e p xk yk := by
    push_cast; rw [add_div, tightCrossInt_cast, tightCrossInt_cast, hrho, hlen, hpref, hsuf]
    rfl
  cases useColl
  · constructor
    · intro _
      unfold checkTightCornerInt at hok
      simp only [Bool.not_false, ↓reduceIte, decide_eq_true_eq] at hok
      have hlt : ((10 ^ 9 * (tightCrossInt rhoS prefS xk + tightCrossInt lenS sufS yk) : ℤ) : ℝ) <
          ((944759996 * dTotTight : ℤ) : ℝ) := by exact_mod_cast hok
      push_cast at hlt
      rw [← hdir_eq, div_lt_iff₀ hdTot_pos]
      push_cast
      linarith only [hlt]
    · intro h; cases h
  · constructor
    · intro h; cases h
    · intro _
      unfold checkTightCornerInt at hok
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hok
      set halfDistS : ℤ := (xik : ℤ) * 10 ^ 8 * lenI
      set distS : ℤ := 2 * halfDistS
      set betaS : ℤ := 2 ^ 17 * 10 ^ 8 * (5080000000 * 2 ^ 16)
      set menuOnesS : ℤ := 2 ^ 17 * pI * (5080000000 * 2 ^ 16 - dI - 1508 * 2 ^ 16)
      set recovInt : ℤ :=
        max 0 (rhoI + eI - 5080000000 * 2 ^ 16) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) +
        (10 ^ 3 * 2 ^ 16) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7)
      have hhalf : (halfDistS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
          (xik : ℝ) / 65536 * tightLen d / 2 := by
        dsimp [halfDistS, lenI, rhoI, d]; unfold tightLen tightRho dCoordTight; push_cast; ring
      have hdist : (distS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
          (xik : ℝ) / 65536 * tightLen d := by
        dsimp [distS, halfDistS, lenI, rhoI, d]; unfold tightLen tightRho dCoordTight; push_cast; ring
      have hbeta : (betaS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) = 508 / 1000 := by
        dsimp [betaS]; unfold dCoordTight; push_cast; ring
      have hmenuOnes : (menuOnesS : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
          p * (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) := by
        dsimp [menuOnesS, d, p]; unfold dCoordTight; push_cast; ring
      have hrecov : (recovInt : ℝ) / (dTotTight : ℝ) =
          max 0 (tightRho d + e - 508 / 1000) + 1 / 10 ^ 7 := by
        have htot : (dTotTight : ℝ) = (dCoordTight : ℝ) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) := by
          unfold dTotTight; push_cast; ring
        have hrec_cast : (recovInt : ℝ) =
            max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 16) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) +
              (10 ^ 3 * 2 ^ 16 : ℝ) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) := by
          dsimp [recovInt]; push_cast; ring_nf
        have hdC_pos : (0 : ℝ) < (dCoordTight : ℝ) := by unfold dCoordTight; positivity
        have hfac : (2 ^ 17 * 10 ^ 8 * 10 ^ 7 : ℝ) ≠ 0 := by norm_num
        rw [hrec_cast, htot, add_div]
        have ht1 : max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 16) *
              (2 ^ 17 * 10 ^ 8 * 10 ^ 7) / ((dCoordTight : ℝ) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7)) =
            max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 16) / (dCoordTight : ℝ) := by
          field_simp [hdC_pos.ne', hfac]
        have ht2 : (10 ^ 3 * 2 ^ 16 : ℝ) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7) /
              ((dCoordTight : ℝ) * (2 ^ 17 * 10 ^ 8 * 10 ^ 7)) = 1 / 10 ^ 7 := by
          unfold dCoordTight; push_cast; ring
        rw [ht1, ht2, max_div_pos' hdC_pos, zero_div]
        congr 2
        dsimp [rhoI, d, e]; unfold tightRho dCoordTight; push_cast; ring
      set nearTotal : ℤ :=
        tightCrossInt rhoS prefS xk + tightCrossInt lenS sufS yk +
        tightCrossInt sufS halfDistS w1k + tightCrossInt (lenS - sufS) halfDistS w0k + recovInt +
        tightCrossInt betaS menuOnesS z2k
      have hnear_eq : (nearTotal : ℝ) / (dTotTight : ℝ) =
          tightNearMenuEnv d e p xk yk xik w1k w0k z2k := by
        dsimp [nearTotal]
        unfold tightNearMenuEnv tightDirectEnv
        push_cast
        simp only [add_div, tightCrossInt_cast, hrecov, hrho, hlen, hpref, hsuf, hhalf, hbeta, hmenuOnes]
        have hsub : ((lenS - sufS : ℤ) : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
            tightLen d - tightSuf d e p := by
          rw [Int.cast_sub, sub_div, hlen, hsuf]
        rw [hsub]
        ring
      set farTotal : ℤ :=
        2 * tightCrossInt rhoS prefS xk + distS * 10 ^ 7 +
        tightCrossInt (lenS - distS) (sufS - halfDistS) qk +
        tightCrossInt betaS menuOnesS z2k
      have hfar_eq : (farTotal : ℝ) / (dTotTight : ℝ) =
          tightFarMenuEnv d e p xk xik qk z2k := by
        dsimp [farTotal]
        unfold tightFarMenuEnv
        push_cast
        simp only [add_div, tightCrossInt_cast, hbeta, hmenuOnes]
        have hsub1 : ((lenS - distS : ℤ) : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
            tightLen d - (xik : ℝ) / 65536 * tightLen d := by
          rw [Int.cast_sub, sub_div, hlen, hdist]
        have hsub2 : ((sufS - halfDistS : ℤ) : ℝ) / ((dCoordTight : ℝ) * 10 ^ 8 * 2 ^ 17) =
            tightSuf d e p - (xik : ℝ) / 65536 * tightLen d / 2 := by
          rw [Int.cast_sub, sub_div, hsuf, hhalf]
        have htwo : 2 * (tightCrossInt rhoS prefS xk : ℝ) / (dTotTight : ℝ) =
            2 * tightCrossEnv (tightRho d) (tightPref d e p) xk := by
          rw [mul_div_assoc, tightCrossInt_cast, hrho, hpref]
        have hdist_term : (distS : ℝ) * 10000000 / (dTotTight : ℝ) =
            (xik : ℝ) / 65536 * tightLen d := by
          rw [← hdist]; unfold dTotTight; push_cast; ring
        rw [htwo, hsub1, hsub2, hdist_term]
      constructor
      · have h1 : (10 ^ 9 : ℝ) * (nearTotal : ℝ) < (2 * 944759996 : ℝ) * (dTotTight : ℝ) := by
          have h1' : ((10 ^ 9 * nearTotal : ℤ) : ℝ) < ((2 * 944759996 * dTotTight : ℤ) : ℝ) := by
            exact_mod_cast hok.1
          push_cast at h1'; linarith only [h1']
        rw [← hnear_eq, div_lt_iff₀ hdTot_pos]
        linarith only [h1]
      · have h2 : (10 ^ 9 : ℝ) * (farTotal : ℝ) < (2 * 944759996 : ℝ) * (dTotTight : ℝ) := by
          have h2' : ((10 ^ 9 * farTotal : ℤ) : ℝ) < ((2 * 944759996 * dTotTight : ℤ) : ℝ) := by
            exact_mod_cast hok.2
          push_cast at h2'; linarith only [h2']
        rw [← hfar_eq, div_lt_iff₀ hdTot_pos]
        linarith only [h2]

private lemma checkTightBSP_sound (tree : BSPTree) :
    ∀ d0 d1 e0 e1 : ℤ, checkTightBSP d0 d1 e0 e1 tree = true →
    ∀ δ d_r p : ℝ,
      (d0 : ℝ) / (dCoordTight : ℝ) ≤ δ ∧ δ ≤ (d1 : ℝ) / (dCoordTight : ℝ) →
      (e0 : ℝ) / (dCoordTight : ℝ) ≤ d_r ∧ d_r ≤ (e1 : ℝ) / (dCoordTight : ℝ) →
      (63092975 : ℝ) / 10 ^ 8 ≤ p ∧ p ≤ (63092976 : ℝ) / 10 ^ 8 →
      ∃ x y xi w₁ w₀ q z₂ : ℝ,
        (1 : ℝ) / 1024 ≤ x ∧ x ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ y ∧ y ≤ 1023 / 1024 ∧
        (1 : ℝ) / 65536 ≤ xi ∧ xi ≤ 65535 / 65536 ∧
        (1 : ℝ) / 1024 ≤ w₁ ∧ w₁ ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ w₀ ∧ w₀ ≤ 1023 / 1024 ∧ w₁ + w₀ ≤ 1 ∧
        (1 : ℝ) / 1024 ≤ q ∧ q ≤ 1023 / 1024 ∧
        (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 1023 / 1024 ∧
        min (tightDirect δ d_r p x y)
          (max ((tightNear δ d_r p x y xi w₁ w₀ + tightMenu δ p z₂) / 2)
               ((tightFar δ d_r p x xi q + tightMenu δ p z₂) / 2)) < 944759996 / 10 ^ 9 := by
  induction tree with
  | leaf useColl xk yk xik w1k w0k qk z2k =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkTightBSP checkTightLeafInt at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨htilts, hc000⟩, hc001⟩, hc010⟩, hc011⟩, hc100⟩, hc101⟩, hc110⟩, hc111⟩ := hok
      obtain ⟨hx1, hx2, hy1, hy2, hxi1, hxi2, hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22,
        hlx1, hlx2, hly1, hly2, hlw11, hlw12, hlw01, hlw02, hlq1, hlq2, hlz1, hlz2⟩ := htilts
      refine ⟨(xk : ℝ) / 1024, (yk : ℝ) / 1024, (xik : ℝ) / 65536,
        (w1k : ℝ) / 1024, (w0k : ℝ) / 1024, (qk : ℝ) / 1024, (z2k : ℝ) / 1024,
        div_le_div_of_nonneg_right (by exact_mod_cast hx1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xk ≤ 1023)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hy1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : yk ≤ 1023)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hxi1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xik ≤ 65535)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hw11) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : w1k ≤ 1023)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hw01) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : w0k ≤ 1023)) (by norm_num),
        by rw [← add_div, div_le_one (by norm_num)]; exact_mod_cast hwsum,
        div_le_div_of_nonneg_right (by exact_mod_cast hq1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : qk ≤ 1023)) (by norm_num),
        by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; exact_mod_cast (by omega : 1024 ≤ z2k * 2),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : z2k ≤ 1023)) (by norm_num), ?_⟩
      have h000 := checkTightCornerInt_sound d0 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc000
      have h001 := checkTightCornerInt_sound d0 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc001
      have h010 := checkTightCornerInt_sound d0 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc010
      have h011 := checkTightCornerInt_sound d0 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc011
      have h100 := checkTightCornerInt_sound d1 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc100
      have h101 := checkTightCornerInt_sound d1 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc101
      have h110 := checkTightCornerInt_sound d1 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc110
      have h111 := checkTightCornerInt_sound d1 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc111
      cases useColl
      · apply lt_of_le_of_lt (min_le_left _ _)
        have hdir_le : tightDirect δ d_r p ((xk : ℝ) / 1024) ((yk : ℝ) / 1024) ≤
            tightDirectEnv δ d_r p xk yk := by
          unfold tightDirect tightDirectEnv
          exact add_le_add (crossEntropy_le_tightCrossEnv _ _ hx1 hx2 hlx1 hlx2)
            (crossEntropy_le_tightCrossEnv _ _ hy1 hy2 hly1 hly2)
        have henv : tightDirectEnv δ d_r p xk yk < 944759996 / 10 ^ 9 :=
          coordConvex_lt_of_corners
            (fun e' p' => tightDirectEnv_convex_d e' p' xk yk)
            (fun d' p' => tightDirectEnv_convex_e d' p' xk yk)
            (fun d' e' => tightDirectEnv_convex_p d' e' xk yk)
            hd he hp
            (h000.1 rfl) (h001.1 rfl) (h010.1 rfl) (h011.1 rfl)
            (h100.1 rfl) (h101.1 rfl) (h110.1 rfl) (h111.1 rfl)
        exact lt_of_le_of_lt hdir_le henv
      · apply lt_of_le_of_lt (min_le_right _ _)
        have hnear_le : tightNear δ d_r p ((xk : ℝ) / 1024) ((yk : ℝ) / 1024) ((xik : ℝ) / 65536)
            ((w1k : ℝ) / 1024) ((w0k : ℝ) / 1024) + tightMenu δ p ((z2k : ℝ) / 1024) ≤
            tightNearMenuEnv δ d_r p xk yk xik w1k w0k z2k := by
          unfold tightNear tightDirect tightMenu tightNearMenuEnv tightDirectEnv
          have h1 := crossEntropy_le_tightCrossEnv (tightRho δ) (tightPref δ d_r p) hx1 hx2 hlx1 hlx2
          have h2 := crossEntropy_le_tightCrossEnv (tightLen δ) (tightSuf δ d_r p) hy1 hy2 hly1 hly2
          have h3 := crossEntropy_le_tightCrossEnv (tightSuf δ d_r p) ((xik : ℝ) / 65536 * tightLen δ / 2) hw11 hw12 hlw11 hlw12
          have h4 := crossEntropy_le_tightCrossEnv (tightLen δ - tightSuf δ d_r p)
            ((xik : ℝ) / 65536 * tightLen δ / 2) hw01 hw02 hlw01 hlw02
          have h5 := crossEntropy_le_tightCrossEnv (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22 hlz1 hlz2
          linarith
        have hfar_le : tightFar δ d_r p ((xk : ℝ) / 1024) ((xik : ℝ) / 65536) ((qk : ℝ) / 1024) +
            tightMenu δ p ((z2k : ℝ) / 1024) ≤ tightFarMenuEnv δ d_r p xk xik qk z2k := by
          unfold tightFar tightMenu tightFarMenuEnv
          have h1 := crossEntropy_le_tightCrossEnv (tightRho δ) (tightPref δ d_r p) hx1 hx2 hlx1 hlx2
          have h2 := crossEntropy_le_tightCrossEnv (tightLen δ - (xik : ℝ) / 65536 * tightLen δ)
            (tightSuf δ d_r p - (xik : ℝ) / 65536 * tightLen δ / 2) hq1 hq2 hlq1 hlq2
          have h3 := crossEntropy_le_tightCrossEnv (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22 hlz1 hlz2
          linarith
        have hnear_lt : tightNearMenuEnv δ d_r p xk yk xik w1k w0k z2k < 2 * (944759996 / 10 ^ 9) :=
          coordConvex_lt_of_corners
            (fun e' p' => tightNearMenuEnv_convex_d e' p' xk yk xik w1k w0k z2k)
            (fun d' p' => tightNearMenuEnv_convex_e d' p' xk yk xik w1k w0k z2k)
            (fun d' e' => tightNearMenuEnv_convex_p d' e' xk yk xik w1k w0k z2k)
            hd he hp
            (h000.2 rfl).1 (h001.2 rfl).1 (h010.2 rfl).1 (h011.2 rfl).1
            (h100.2 rfl).1 (h101.2 rfl).1 (h110.2 rfl).1 (h111.2 rfl).1
        have hfar_lt : tightFarMenuEnv δ d_r p xk xik qk z2k < 2 * (944759996 / 10 ^ 9) :=
          coordConvex_lt_of_corners
            (fun e' p' => tightFarMenuEnv_convex_d e' p' xk xik qk z2k)
            (fun d' p' => tightFarMenuEnv_convex_e d' p' xk xik qk z2k)
            (fun d' e' => tightFarMenuEnv_convex_p d' e' xk xik qk z2k)
            hd he hp
            (h000.2 rfl).2 (h001.2 rfl).2 (h010.2 rfl).2 (h011.2 rfl).2
            (h100.2 rfl).2 (h101.2 rfl).2 (h110.2 rfl).2 (h111.2 rfl).2
        apply max_lt <;> linarith
  | splitD l r ihl ihr =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkTightBSP at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hl⟩, hr⟩ := hok
      set mid := (d0 + d1) / 2
      by_cases hle : δ ≤ (mid : ℝ) / (dCoordTight : ℝ)
      · exact ihl d0 mid e0 e1 hl δ d_r p ⟨hd.1, hle⟩ he hp
      · exact ihr mid d1 e0 e1 hr δ d_r p ⟨le_of_not_ge hle, hd.2⟩ he hp
  | splitE l r ihl ihr =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkTightBSP at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hl⟩, hr⟩ := hok
      set mid := (e0 + e1) / 2
      by_cases hle : d_r ≤ (mid : ℝ) / (dCoordTight : ℝ)
      · exact ihl d0 d1 e0 mid hl δ d_r p hd ⟨he.1, hle⟩ hp
      · exact ihr d0 d1 mid e1 hr δ d_r p hd ⟨le_of_not_ge hle, he.2⟩ hp

/-- **Complete Pure-Kernel Tight-Slack `0.05524` (`< 0.944759996 < 0.94476`) Uniform Certificate Theorem:**
For EVERY `(δ, d_r) ∈ [-10^{-7}, 0.012] × [-10^{-7}, 1]` and `p = log_3 2`, there exist valid
tilts `x, y, w₁, w₀, q, z₂ ∈ [1/1024, 1023/1024]` (`w₁ + w₀ ≤ 1`, `1/2 ≤ z₂`) and
`xi ∈ [1/65536, 65535/65536]` certifying
`min(U, max((N + M_2)/2, (F + M_2)/2)) < 944759996 / 10^9` (preserving `> 4 * 10^{-9}` headroom
below `0.94476` for `prefactor_absorption_ge_two_pow_40`). -/
theorem tight_slack_005524_uniform_bound (δ d_r : ℝ)
    (hδ : -(1 / 10 ^ 7 : ℝ) ≤ δ ∧ δ ≤ 12 / 1000)
    (hd_r : -(1 / 10 ^ 7 : ℝ) ≤ d_r ∧ d_r ≤ 1) :
    let p := Real.log 2 / Real.log 3
    ∃ x y xi w₁ w₀ q z₂ : ℝ,
      (1 : ℝ) / 1024 ≤ x ∧ x ≤ 1023 / 1024 ∧
      (1 : ℝ) / 1024 ≤ y ∧ y ≤ 1023 / 1024 ∧
      (1 : ℝ) / 65536 ≤ xi ∧ xi ≤ 65535 / 65536 ∧
      (1 : ℝ) / 1024 ≤ w₁ ∧ w₁ ≤ 1023 / 1024 ∧
      (1 : ℝ) / 1024 ≤ w₀ ∧ w₀ ≤ 1023 / 1024 ∧ w₁ + w₀ ≤ 1 ∧
      (1 : ℝ) / 1024 ≤ q ∧ q ≤ 1023 / 1024 ∧
      (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 1023 / 1024 ∧
      min (tightDirect δ d_r p x y)
        (max ((tightNear δ d_r p x y xi w₁ w₀ + tightMenu δ p z₂) / 2)
             ((tightFar δ d_r p x xi q + tightMenu δ p z₂) / 2)) < 944759996 / 10 ^ 9 := by
  intro p
  have hp := log3_two_bounds
  have hd_cast : ((-10 ^ 3 * 2 ^ 16 : ℤ) : ℝ) / (dCoordTight : ℝ) ≤ δ ∧
      δ ≤ ((12 * 10 ^ 7 * 2 ^ 16 : ℤ) : ℝ) / (dCoordTight : ℝ) := by
    unfold dCoordTight; push_cast; constructor <;> linarith
  have he_cast : ((-10 ^ 3 * 2 ^ 16 : ℤ) : ℝ) / (dCoordTight : ℝ) ≤ d_r ∧
      d_r ≤ ((10 ^ 10 * 2 ^ 16 : ℤ) : ℝ) / (dCoordTight : ℝ) := by
    unfold dCoordTight; push_cast; constructor <;> linarith
  exact checkTightBSP_sound tightSlackBSP
    (-10 ^ 3 * 2 ^ 16) (12 * 10 ^ 7 * 2 ^ 16)
    (-10 ^ 3 * 2 ^ 16) (10 ^ 10 * 2 ^ 16)
    tightSlackBSP_ok δ d_r p hd_cast he_cast ⟨hp.1.le, hp.2.le⟩

/-! ## 5. Tilt-Floor Companion to `wideSlackBSP_ok` (`[1/512, 511/512]`, `< 9449 / 10000`) -/

private lemma crossEntropy_le_crossEnv' (a j : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 512) :
    crossEntropy a j ((k : ℝ) / 512) ≤ crossEnv a j k := by
  have hk := logTable512_sound hk1 hk2
  have hkc := logTable512_sound (k := 512 - k) (by omega) (by omega)
  have hcomp : 1 - (k : ℝ) / 512 = ((512 - k : ℕ) : ℝ) / 512 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : j * (-Real.logb 2 ((k : ℝ) / 512)) ≤ costEnv j k := by
    unfold costEnv
    by_cases hj : 0 ≤ j
    · exact le_trans (mul_le_mul_of_nonneg_left hk.2 hj) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hk.1 (le_of_not_ge hj)) (le_max_left _ _)
  have h2 : (a - j) * (-Real.logb 2 (1 - (k : ℝ) / 512)) ≤ costEnv (a - j) (512 - k) := by
    rw [hcomp]
    unfold costEnv
    by_cases hj : 0 ≤ a - j
    · exact le_trans (mul_le_mul_of_nonneg_left hkc.2 hj) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hkc.1 (le_of_not_ge hj)) (le_max_left _ _)
  unfold crossEntropy crossEnv
  linarith

private lemma isConvexR_costEnv_affine' (m c : ℝ) (k : ℕ) :
    IsConvexR (fun x => costEnv (m * x + c) k) := by
  unfold costEnv
  apply isConvexR_max'
  · have h := isConvexR_affine' (m * ((logLo k : ℝ) / 10 ^ 6)) (c * ((logLo k : ℝ) / 10 ^ 6))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith
  · have h := isConvexR_affine' (m * ((logHi k : ℝ) / 10 ^ 6)) (c * ((logHi k : ℝ) / 10 ^ 6))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith

private lemma isConvexR_crossEnv_affine' (m₁ c₁ m₂ c₂ : ℝ) (k : ℕ) :
    IsConvexR (fun x => crossEnv (m₁ * x + c₁) (m₂ * x + c₂) k) := by
  unfold crossEnv
  apply isConvexR_add'
  · exact isConvexR_costEnv_affine' m₂ c₂ k
  · have h := isConvexR_costEnv_affine' (m₁ - m₂) (c₁ - c₂) (512 - k)
    intro a b t ht0 ht1
    have := h a b t ht0 ht1
    have heq : ∀ y : ℝ, (m₁ - m₂) * y + (c₁ - c₂) = m₁ * y + c₁ - (m₂ * y + c₂) := fun y => by ring
    simpa [heq] using this

private lemma wideDirectEnv_convex_d' (e p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun d => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)
        p (p * (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) xk) (fun x => ?_)
    unfold widePref wideRho; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' (-1) (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4))
        0 (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e))) yk) (fun x => ?_)
    unfold wideLen wideSuf widePref wideRho; congr 1 <;> ring

private lemma wideDirectEnv_convex_e' (d p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun e => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (wideRho d) p (p * wideRho d) xk) (fun x => ?_)
    unfold widePref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (wideLen d) (-p) (p * (1 + d) - p * wideRho d) yk) (fun x => ?_)
    unfold wideSuf widePref; congr 1 <;> ring

private lemma wideDirectEnv_convex_p' (d e : ℝ) (xk yk : ℕ) :
    IsConvexR (fun p => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add'
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (wideRho d) (wideRho d + e) 0 xk) (fun x => ?_)
    unfold widePref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (wideLen d) (1 + d - (wideRho d + e)) 0 yk) (fun x => ?_)
    unfold wideSuf widePref; congr 1 <;> ring

private lemma wideNearMenuEnv_convex_d' (e p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun d => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact wideDirectEnv_convex_d' e p xk yk
          · refine isConvexR_congr'
              (isConvexR_crossEnv_affine' 0 (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)))
                (-((xik : ℝ) / 512 / 2))
                ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) w1k)
              (fun x => ?_)
            unfold wideSuf widePref wideLen wideRho; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_crossEnv_affine' (-1)
              (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4) -
                p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)))
              (-((xik : ℝ) / 512 / 2))
              ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) w0k)
            (fun x => ?_)
          unfold wideLen wideSuf widePref wideRho; congr 1 <;> ring
      · apply isConvexR_max' (isConvexR_const' 0)
        refine isConvexR_congr'
          (isConvexR_affine' 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e - 508 / 1000))
          (fun x => by unfold wideRho; ring)
    · exact isConvexR_const' (1 / 10 ^ 7)
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma wideNearMenuEnv_convex_e' (d p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun e => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact wideDirectEnv_convex_e' d p xk yk
          · refine isConvexR_congr'
              (isConvexR_crossEnv_affine' (-p) (p * (1 + d) - p * wideRho d)
                0 ((xik : ℝ) / 512 * wideLen d / 2) w1k) (fun x => ?_)
            unfold wideSuf widePref; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_crossEnv_affine' p (wideLen d - (p * (1 + d) - p * wideRho d))
              0 ((xik : ℝ) / 512 * wideLen d / 2) w0k) (fun x => ?_)
          unfold wideSuf widePref; congr 1 <;> ring
      · apply isConvexR_max' (isConvexR_const' 0)
        refine isConvexR_congr' (isConvexR_affine' 1 (wideRho d - 508 / 1000)) (fun _ => by ring)
    · exact isConvexR_const' (1 / 10 ^ 7)
  · exact isConvexR_const' _

private lemma wideNearMenuEnv_convex_p' (d e : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun p => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_add'
        · apply isConvexR_add'
          · exact wideDirectEnv_convex_p' d e xk yk
          · refine isConvexR_congr'
              (isConvexR_crossEnv_affine' (1 + d - (wideRho d + e)) 0
                0 ((xik : ℝ) / 512 * wideLen d / 2) w1k) (fun x => ?_)
            unfold wideSuf widePref; congr 1 <;> ring
        · refine isConvexR_congr'
            (isConvexR_crossEnv_affine' (-(1 + d - (wideRho d + e))) (wideLen d)
              0 ((xik : ℝ) / 512 * wideLen d / 2) w0k) (fun x => ?_)
          unfold wideSuf widePref; congr 1 <;> ring
      · exact isConvexR_const' _
    · exact isConvexR_const' (1 / 10 ^ 7)
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma wideFarMenuEnv_convex_d' (e p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun d => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_crossEnv_affine' 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)
            p (p * (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) xk) (fun x => ?_)
        unfold widePref wideRho; congr 1 <;> ring
      · refine isConvexR_congr'
          (isConvexR_affine' (-((xik : ℝ) / 512))
            ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4))))
          (fun x => by unfold wideLen wideRho; ring)
    · refine isConvexR_congr'
        (isConvexR_crossEnv_affine' (-(1 - (xik : ℝ) / 512))
          ((1 - (xik : ℝ) / 512) * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)))
          ((xik : ℝ) / 512 / 2)
          (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) -
            (xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) qk)
        (fun x => ?_)
      unfold wideSuf widePref wideLen wideRho; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma wideFarMenuEnv_convex_e' (d p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun e => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_crossEnv_affine' 0 (wideRho d) p (p * wideRho d) xk) (fun x => ?_)
        unfold widePref; congr 1 <;> ring
      · exact isConvexR_const' _
    · refine isConvexR_congr'
        (isConvexR_crossEnv_affine' 0 (wideLen d - (xik : ℝ) / 512 * wideLen d)
          (-p) (p * (1 + d) - p * wideRho d - (xik : ℝ) / 512 * wideLen d / 2) qk) (fun x => ?_)
      unfold wideSuf widePref; congr 1 <;> ring
  · exact isConvexR_const' _

private lemma wideFarMenuEnv_convex_p' (d e : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun p => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add'
  · apply isConvexR_add'
    · apply isConvexR_add'
      · apply isConvexR_const_mul' (by norm_num)
        refine isConvexR_congr'
          (isConvexR_crossEnv_affine' 0 (wideRho d) (wideRho d + e) 0 xk) (fun x => ?_)
        unfold widePref; congr 1 <;> ring
      · exact isConvexR_const' _
    · refine isConvexR_congr'
        (isConvexR_crossEnv_affine' 0 (wideLen d - (xik : ℝ) / 512 * wideLen d)
          (1 + d - (wideRho d + e)) (-((xik : ℝ) / 512 * wideLen d / 2)) qk) (fun x => ?_)
      unfold wideSuf widePref; congr 1 <;> ring
  · refine isConvexR_congr'
      (isConvexR_crossEnv_affine' 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma costInt_cast' (cS : ℤ) (k : ℕ) :
    (costInt cS k : ℝ) / (dTot : ℝ) = costEnv ((cS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024)) k := by
  unfold costInt costEnv
  have hd_pos : (0 : ℝ) < (dTot : ℝ) := by unfold dTot dCoord; positivity
  have hcast : ((max (cS * (logLo k : ℤ)) (cS * (logHi k : ℤ)) : ℤ) : ℝ) =
      max ((cS : ℝ) * (logLo k : ℝ)) ((cS : ℝ) * (logHi k : ℝ)) := by push_cast; rfl
  rw [hcast, max_div_pos' hd_pos]
  unfold dTot
  push_cast
  congr 1 <;> ring

private lemma crossInt_cast' (lenS onesS : ℤ) (k : ℕ) :
    (crossInt lenS onesS k : ℝ) / (dTot : ℝ) =
      crossEnv ((lenS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024))
        ((onesS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024)) k := by
  unfold crossInt crossEnv
  push_cast
  rw [add_div, costInt_cast', costInt_cast']
  congr 2
  push_cast
  ring

private lemma checkCornerInt_sound' (dI eI pI : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ)
    (hok : checkCornerInt dI eI pI useColl xk yk xik w1k w0k qk z2k = true) :
    let d : ℝ := (dI : ℝ) / (dCoord : ℝ)
    let e : ℝ := (eI : ℝ) / (dCoord : ℝ)
    let p : ℝ := (pI : ℝ) / 10 ^ 8
    (useColl = false → directEnv d e p xk yk < 9449 / 10000) ∧
    (useColl = true →
      nearMenuEnv d e p xk yk xik w1k w0k z2k < 2 * (9449 / 10000) ∧
      farMenuEnv d e p xk xik qk z2k < 2 * (9449 / 10000)) := by
  intro d e p
  have hdTot_pos : (0 : ℝ) < (dTot : ℝ) := by unfold dTot dCoord; positivity
  set rhoI : ℤ := 4921003000 * 2 ^ 14 + dI
  set lenI : ℤ := dCoord - rhoI
  set rhoS : ℤ := 1024 * 10 ^ 8 * rhoI
  set lenS : ℤ := 1024 * 10 ^ 8 * lenI
  set prefS : ℤ := 1024 * pI * (rhoI + eI)
  set sufS : ℤ := 1024 * pI * (dCoord + dI) - prefS
  have hrho : (rhoS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) = wideRho d := by
    dsimp [rhoS, rhoI, d]; unfold wideRho dCoord; push_cast; ring
  have hlen : (lenS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) = wideLen d := by
    dsimp [lenS, lenI, rhoI, d]; unfold wideLen wideRho dCoord; push_cast; ring
  have hpref : (prefS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) = widePref d e p := by
    dsimp [prefS, rhoI, d, e, p]; unfold widePref wideRho dCoord; push_cast; ring
  have hsuf : (sufS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) = wideSuf d e p := by
    dsimp [sufS, prefS, rhoI, d, e, p]; unfold wideSuf widePref wideRho dCoord; push_cast; ring
  have hdir_eq : ((crossInt rhoS prefS xk + crossInt lenS sufS yk : ℤ) : ℝ) / (dTot : ℝ) =
      directEnv d e p xk yk := by
    push_cast; rw [add_div, crossInt_cast', crossInt_cast', hrho, hlen, hpref, hsuf]; rfl
  cases useColl
  · constructor
    · intro _
      unfold checkCornerInt at hok
      simp only [Bool.not_false, ↓reduceIte, decide_eq_true_eq] at hok
      have hlt : ((10000 * (crossInt rhoS prefS xk + crossInt lenS sufS yk) : ℤ) : ℝ) <
          ((9449 * dTot : ℤ) : ℝ) := by exact_mod_cast hok
      push_cast at hlt
      rw [← hdir_eq, div_lt_iff₀ hdTot_pos]
      push_cast
      linarith only [hlt]
    · intro h; cases h
  · constructor
    · intro h; cases h
    · intro _
      unfold checkCornerInt at hok
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hok
      set halfDistS : ℤ := (xik : ℤ) * 10 ^ 8 * lenI
      set distS : ℤ := 2 * halfDistS
      set betaS : ℤ := 1024 * 10 ^ 8 * (5080000000 * 2 ^ 14)
      set menuOnesS : ℤ := 1024 * pI * (5080000000 * 2 ^ 14 - dI - 1508 * 2 ^ 14)
      set recovInt : ℤ :=
        max 0 (rhoI + eI - 5080000000 * 2 ^ 14) * (1024 * 10 ^ 8 * 10 ^ 6) +
        (10 ^ 3 * 2 ^ 14) * (1024 * 10 ^ 8 * 10 ^ 6)
      have hhalf : (halfDistS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
          (xik : ℝ) / 512 * wideLen d / 2 := by
        dsimp [halfDistS, lenI, rhoI, d]; unfold wideLen wideRho dCoord; push_cast; ring
      have hdist : (distS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
          (xik : ℝ) / 512 * wideLen d := by
        dsimp [distS, halfDistS, lenI, rhoI, d]; unfold wideLen wideRho dCoord; push_cast; ring
      have hbeta : (betaS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) = 508 / 1000 := by
        dsimp [betaS]; unfold dCoord; push_cast; ring
      have hmenuOnes : (menuOnesS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
          p * (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) := by
        dsimp [menuOnesS, d, p]; unfold dCoord; push_cast; ring
      have hrecov : (recovInt : ℝ) / (dTot : ℝ) =
          max 0 (wideRho d + e - 508 / 1000) + 1 / 10 ^ 7 := by
        have htot : (dTot : ℝ) = (dCoord : ℝ) * (1024 * 10 ^ 8 * 10 ^ 6) := by
          unfold dTot; push_cast; ring
        have hrec_cast : (recovInt : ℝ) =
            max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 14) * (1024 * 10 ^ 8 * 10 ^ 6) +
              (10 ^ 3 * 2 ^ 14 : ℝ) * (1024 * 10 ^ 8 * 10 ^ 6) := by
          dsimp [recovInt]; push_cast; ring_nf
        have hdC_pos : (0 : ℝ) < (dCoord : ℝ) := by unfold dCoord; positivity
        have hfac : (1024 * 10 ^ 8 * 10 ^ 6 : ℝ) ≠ 0 := by norm_num
        rw [hrec_cast, htot, add_div]
        have ht1 : max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 14) *
              (1024 * 10 ^ 8 * 10 ^ 6) / ((dCoord : ℝ) * (1024 * 10 ^ 8 * 10 ^ 6)) =
            max (0 : ℝ) ((rhoI : ℝ) + (eI : ℝ) - 5080000000 * 2 ^ 14) / (dCoord : ℝ) := by
          field_simp [hdC_pos.ne', hfac]
        have ht2 : (10 ^ 3 * 2 ^ 14 : ℝ) * (1024 * 10 ^ 8 * 10 ^ 6) /
              ((dCoord : ℝ) * (1024 * 10 ^ 8 * 10 ^ 6)) = 1 / 10 ^ 7 := by
          unfold dCoord; push_cast; ring
        rw [ht1, ht2, max_div_pos' hdC_pos, zero_div]
        congr 2
        dsimp [rhoI, d, e]; unfold wideRho dCoord; push_cast; ring
      set nearTotal : ℤ :=
        crossInt rhoS prefS xk + crossInt lenS sufS yk +
        crossInt sufS halfDistS w1k + crossInt (lenS - sufS) halfDistS w0k + recovInt +
        crossInt betaS menuOnesS z2k
      have hnear_eq : (nearTotal : ℝ) / (dTot : ℝ) =
          nearMenuEnv d e p xk yk xik w1k w0k z2k := by
        dsimp [nearTotal]
        unfold nearMenuEnv directEnv
        push_cast
        simp only [add_div, crossInt_cast', hrecov, hrho, hlen, hpref, hsuf, hhalf, hbeta, hmenuOnes]
        have hsub : ((lenS - sufS : ℤ) : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
            wideLen d - wideSuf d e p := by
          rw [Int.cast_sub, sub_div, hlen, hsuf]
        rw [hsub]
        ring
      set farTotal : ℤ :=
        2 * crossInt rhoS prefS xk + distS * 10 ^ 6 +
        crossInt (lenS - distS) (sufS - halfDistS) qk +
        crossInt betaS menuOnesS z2k
      have hfar_eq : (farTotal : ℝ) / (dTot : ℝ) =
          farMenuEnv d e p xk xik qk z2k := by
        dsimp [farTotal]
        unfold farMenuEnv
        push_cast
        simp only [add_div, crossInt_cast', hbeta, hmenuOnes]
        have hsub1 : ((lenS - distS : ℤ) : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
            wideLen d - (xik : ℝ) / 512 * wideLen d := by
          rw [Int.cast_sub, sub_div, hlen, hdist]
        have hsub2 : ((sufS - halfDistS : ℤ) : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
            wideSuf d e p - (xik : ℝ) / 512 * wideLen d / 2 := by
          rw [Int.cast_sub, sub_div, hsuf, hhalf]
        have htwo : 2 * (crossInt rhoS prefS xk : ℝ) / (dTot : ℝ) =
            2 * crossEnv (wideRho d) (widePref d e p) xk := by
          rw [mul_div_assoc, crossInt_cast', hrho, hpref]
        have hdist_term : (distS : ℝ) * 1000000 / (dTot : ℝ) =
            (xik : ℝ) / 512 * wideLen d := by
          rw [← hdist]; unfold dTot; push_cast; ring
        rw [htwo, hsub1, hsub2, hdist_term]
      constructor
      · have h1 : (10000 : ℝ) * (nearTotal : ℝ) < (2 * 9449 : ℝ) * (dTot : ℝ) := by
          have h1' : ((10000 * nearTotal : ℤ) : ℝ) < ((2 * 9449 * dTot : ℤ) : ℝ) := by
            exact_mod_cast hok.1
          push_cast at h1'; linarith only [h1']
        rw [← hnear_eq, div_lt_iff₀ hdTot_pos]; linarith only [h1]
      · have h2 : (10000 : ℝ) * (farTotal : ℝ) < (2 * 9449 : ℝ) * (dTot : ℝ) := by
          have h2' : ((10000 * farTotal : ℤ) : ℝ) < ((2 * 9449 * dTot : ℤ) : ℝ) := by
            exact_mod_cast hok.2
          push_cast at h2'; linarith only [h2']
        rw [← hfar_eq, div_lt_iff₀ hdTot_pos]; linarith only [h2]

private lemma checkBSP_sound_with_floor (tree : BSPTree) :
    ∀ d0 d1 e0 e1 : ℤ, checkBSP d0 d1 e0 e1 tree = true →
    ∀ δ d_r p : ℝ,
      (d0 : ℝ) / (dCoord : ℝ) ≤ δ ∧ δ ≤ (d1 : ℝ) / (dCoord : ℝ) →
      (e0 : ℝ) / (dCoord : ℝ) ≤ d_r ∧ d_r ≤ (e1 : ℝ) / (dCoord : ℝ) →
      (63092975 : ℝ) / 10 ^ 8 ≤ p ∧ p ≤ (63092976 : ℝ) / 10 ^ 8 →
      ∃ x y xi w₁ w₀ q z₂ : ℝ,
        (1 : ℝ) / 512 ≤ x ∧ x ≤ 511 / 512 ∧
        (1 : ℝ) / 512 ≤ y ∧ y ≤ 511 / 512 ∧
        (1 : ℝ) / 512 ≤ xi ∧ xi ≤ 511 / 512 ∧
        (1 : ℝ) / 512 ≤ w₁ ∧ w₁ ≤ 511 / 512 ∧
        (1 : ℝ) / 512 ≤ w₀ ∧ w₀ ≤ 511 / 512 ∧ w₁ + w₀ ≤ 1 ∧
        (1 : ℝ) / 512 ≤ q ∧ q ≤ 511 / 512 ∧
        (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 511 / 512 ∧
        min (wideDirect δ d_r p x y)
          (max ((wideNear δ d_r p x y xi w₁ w₀ + wideMenu δ p z₂) / 2)
               ((wideFar δ d_r p x xi q + wideMenu δ p z₂) / 2)) < 9449 / 10000 := by
  induction tree with
  | leaf useColl xk yk xik w1k w0k qk z2k =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkBSP checkLeafInt at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨htilts, hc000⟩, hc001⟩, hc010⟩, hc011⟩, hc100⟩, hc101⟩, hc110⟩, hc111⟩ := hok
      obtain ⟨hx1, hx2, hy1, hy2, hxi1, hxi2, hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22⟩ :=
        htilts
      refine ⟨(xk : ℝ) / 512, (yk : ℝ) / 512, (xik : ℝ) / 512,
        (w1k : ℝ) / 512, (w0k : ℝ) / 512, (qk : ℝ) / 512, (z2k : ℝ) / 512,
        div_le_div_of_nonneg_right (by exact_mod_cast hx1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xk ≤ 511)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hy1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : yk ≤ 511)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hxi1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xik ≤ 511)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hw11) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : w1k ≤ 511)) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast hw01) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : w0k ≤ 511)) (by norm_num),
        by rw [← add_div, div_le_one (by norm_num)]; exact_mod_cast hwsum,
        div_le_div_of_nonneg_right (by exact_mod_cast hq1) (by norm_num),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : qk ≤ 511)) (by norm_num),
        by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; exact_mod_cast (by omega : 512 ≤ z2k * 2),
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : z2k ≤ 511)) (by norm_num), ?_⟩
      have h000 := checkCornerInt_sound' d0 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc000
      have h001 := checkCornerInt_sound' d0 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc001
      have h010 := checkCornerInt_sound' d0 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc010
      have h011 := checkCornerInt_sound' d0 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc011
      have h100 := checkCornerInt_sound' d1 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc100
      have h101 := checkCornerInt_sound' d1 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc101
      have h110 := checkCornerInt_sound' d1 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc110
      have h111 := checkCornerInt_sound' d1 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc111
      cases useColl
      · apply lt_of_le_of_lt (min_le_left _ _)
        have hdir_le : wideDirect δ d_r p ((xk : ℝ) / 512) ((yk : ℝ) / 512) ≤
            directEnv δ d_r p xk yk := by
          unfold wideDirect directEnv
          exact add_le_add (crossEntropy_le_crossEnv' _ _ hx1 hx2)
            (crossEntropy_le_crossEnv' _ _ hy1 hy2)
        have henv : directEnv δ d_r p xk yk < 9449 / 10000 :=
          coordConvex_lt_of_corners
            (fun e' p' => wideDirectEnv_convex_d' e' p' xk yk)
            (fun d' p' => wideDirectEnv_convex_e' d' p' xk yk)
            (fun d' e' => wideDirectEnv_convex_p' d' e' xk yk)
            hd he hp
            (h000.1 rfl) (h001.1 rfl) (h010.1 rfl) (h011.1 rfl)
            (h100.1 rfl) (h101.1 rfl) (h110.1 rfl) (h111.1 rfl)
        exact lt_of_le_of_lt hdir_le henv
      · apply lt_of_le_of_lt (min_le_right _ _)
        have hnear_le : wideNear δ d_r p ((xk : ℝ) / 512) ((yk : ℝ) / 512) ((xik : ℝ) / 512)
            ((w1k : ℝ) / 512) ((w0k : ℝ) / 512) + wideMenu δ p ((z2k : ℝ) / 512) ≤
            nearMenuEnv δ d_r p xk yk xik w1k w0k z2k := by
          unfold wideNear wideDirect wideMenu nearMenuEnv directEnv
          have h1 := crossEntropy_le_crossEnv' (wideRho δ) (widePref δ d_r p) hx1 hx2
          have h2 := crossEntropy_le_crossEnv' (wideLen δ) (wideSuf δ d_r p) hy1 hy2
          have h3 := crossEntropy_le_crossEnv' (wideSuf δ d_r p) ((xik : ℝ) / 512 * wideLen δ / 2) hw11 hw12
          have h4 := crossEntropy_le_crossEnv' (wideLen δ - wideSuf δ d_r p)
            ((xik : ℝ) / 512 * wideLen δ / 2) hw01 hw02
          have h5 := crossEntropy_le_crossEnv' (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22
          linarith
        have hfar_le : wideFar δ d_r p ((xk : ℝ) / 512) ((xik : ℝ) / 512) ((qk : ℝ) / 512) +
            wideMenu δ p ((z2k : ℝ) / 512) ≤ farMenuEnv δ d_r p xk xik qk z2k := by
          unfold wideFar wideMenu farMenuEnv
          have h1 := crossEntropy_le_crossEnv' (wideRho δ) (widePref δ d_r p) hx1 hx2
          have h2 := crossEntropy_le_crossEnv' (wideLen δ - (xik : ℝ) / 512 * wideLen δ)
            (wideSuf δ d_r p - (xik : ℝ) / 512 * wideLen δ / 2) hq1 hq2
          have h3 := crossEntropy_le_crossEnv' (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22
          linarith
        have hnear_lt : nearMenuEnv δ d_r p xk yk xik w1k w0k z2k < 2 * (9449 / 10000) :=
          coordConvex_lt_of_corners
            (fun e' p' => wideNearMenuEnv_convex_d' e' p' xk yk xik w1k w0k z2k)
            (fun d' p' => wideNearMenuEnv_convex_e' d' p' xk yk xik w1k w0k z2k)
            (fun d' e' => wideNearMenuEnv_convex_p' d' e' xk yk xik w1k w0k z2k)
            hd he hp
            (h000.2 rfl).1 (h001.2 rfl).1 (h010.2 rfl).1 (h011.2 rfl).1
            (h100.2 rfl).1 (h101.2 rfl).1 (h110.2 rfl).1 (h111.2 rfl).1
        have hfar_lt : farMenuEnv δ d_r p xk xik qk z2k < 2 * (9449 / 10000) :=
          coordConvex_lt_of_corners
            (fun e' p' => wideFarMenuEnv_convex_d' e' p' xk xik qk z2k)
            (fun d' p' => wideFarMenuEnv_convex_e' d' p' xk xik qk z2k)
            (fun d' e' => wideFarMenuEnv_convex_p' d' e' xk xik qk z2k)
            hd he hp
            (h000.2 rfl).2 (h001.2 rfl).2 (h010.2 rfl).2 (h011.2 rfl).2
            (h100.2 rfl).2 (h101.2 rfl).2 (h110.2 rfl).2 (h111.2 rfl).2
        apply max_lt <;> linarith
  | splitD l r ihl ihr =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkBSP at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hl⟩, hr⟩ := hok
      set mid := (d0 + d1) / 2
      by_cases hle : δ ≤ (mid : ℝ) / (dCoord : ℝ)
      · exact ihl d0 mid e0 e1 hl δ d_r p ⟨hd.1, hle⟩ he hp
      · exact ihr mid d1 e0 e1 hr δ d_r p ⟨le_of_not_ge hle, hd.2⟩ he hp
  | splitE l r ihl ihr =>
      intro d0 d1 e0 e1 hok δ d_r p hd he hp
      unfold checkBSP at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hl⟩, hr⟩ := hok
      set mid := (e0 + e1) / 2
      by_cases hle : d_r ≤ (mid : ℝ) / (dCoord : ℝ)
      · exact ihl d0 d1 e0 mid hl δ d_r p hd ⟨he.1, hle⟩ hp
      · exact ihr d0 d1 mid e1 hr δ d_r p hd ⟨le_of_not_ge hle, he.2⟩ hp

/-- Lift of `wideSlackBSP_ok` exposing the explicit `[1/512, 511/512]` tilt floor for
rounding-error absorption in the slice-to-shell assembly. -/
theorem wide_slack_0055_uniform_bound_with_floor (δ d_r : ℝ)
    (hδ : -(1 / 10 ^ 7 : ℝ) ≤ δ ∧ δ ≤ 12 / 1000)
    (hd_r : -(1 / 10 ^ 7 : ℝ) ≤ d_r ∧ d_r ≤ 1) :
    let p := Real.log 2 / Real.log 3
    ∃ x y xi w₁ w₀ q z₂ : ℝ,
      (1 : ℝ) / 512 ≤ x ∧ x ≤ 511 / 512 ∧
      (1 : ℝ) / 512 ≤ y ∧ y ≤ 511 / 512 ∧
      (1 : ℝ) / 512 ≤ xi ∧ xi ≤ 511 / 512 ∧
      (1 : ℝ) / 512 ≤ w₁ ∧ w₁ ≤ 511 / 512 ∧
      (1 : ℝ) / 512 ≤ w₀ ∧ w₀ ≤ 511 / 512 ∧ w₁ + w₀ ≤ 1 ∧
      (1 : ℝ) / 512 ≤ q ∧ q ≤ 511 / 512 ∧
      (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 511 / 512 ∧
      min (wideDirect δ d_r p x y)
        (max ((wideNear δ d_r p x y xi w₁ w₀ + wideMenu δ p z₂) / 2)
             ((wideFar δ d_r p x xi q + wideMenu δ p z₂) / 2)) < 9449 / 10000 := by
  intro p
  have hp := log3_two_bounds
  have hd_cast : ((-10 ^ 3 * 2 ^ 14 : ℤ) : ℝ) / (dCoord : ℝ) ≤ δ ∧
      δ ≤ ((12 * 10 ^ 7 * 2 ^ 14 : ℤ) : ℝ) / (dCoord : ℝ) := by
    unfold dCoord; push_cast; constructor <;> linarith
  have he_cast : ((-10 ^ 3 * 2 ^ 14 : ℤ) : ℝ) / (dCoord : ℝ) ≤ d_r ∧
      d_r ≤ ((10 ^ 10 * 2 ^ 14 : ℤ) : ℝ) / (dCoord : ℝ) := by
    unfold dCoord; push_cast; constructor <;> linarith
  exact checkBSP_sound_with_floor wideSlackBSP
    (-10 ^ 3 * 2 ^ 14) (12 * 10 ^ 7 * 2 ^ 14)
    (-10 ^ 3 * 2 ^ 14) (10 ^ 10 * 2 ^ 14)
    wideSlackBSP_ok δ d_r p hd_cast he_cast ⟨hp.1.le, hp.2.le⟩

end CollatzTwoWindow
