module

public import CollatzTwoWindow.Certificates
public import CollatzTwoWindow.WideSlackCertData

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pure-Kernel Verification of the Wide-Slack (`σ = 10^{-4}`, Exponent `0.945`) Rectangle Cover

Verifies the complete 202-rectangle binary space partition certificate covering
`(δ, d_r) ∈ [-10^{-7}, 0.012] × [-10^{-7}, 1]` at separation slack `σ = 10^{-4}`,
proving unconditionally in the Lean 4 kernel (ZERO `sorry`, ZERO `native_decide`):

- `logTable512_sound`: every entry `1 ≤ k < 512` of `logTable512` encloses
  `-Real.logb 2 (k / 512)` to precision `10^{-6}` via pure-`Nat` 5-term `atanh` checks.
- `wide_slack_0055_uniform_bound`: for EVERY `(δ, d_r) ∈ [-10^{-7}, 0.012] × [-10^{-7}, 1]`,
  at `p = Real.log 2 / Real.log 3`, there exist valid tilts `x, y, xi, w₁, w₀, q, z₂ ∈ (0, 1)`
  with `w₁ + w₀ ≤ 1` and `1/2 ≤ z₂` such that
  `min (wideDirect δ d_r p x y) (max ((wideNear ... + wideMenu ...) / 2) ((wideFar ... + wideMenu ...) / 2)) < 9449 / 10000`,
  leaving strictly more than `10^{-4}` of margin below `0.945`.
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Exact Real-Valued Slice Exponents (`classical-tilted-passage.md`) -/

noncomputable def wideRho (δ : ℝ) : ℝ :=
  492 / 1000 + δ + 3 / 10 ^ 7 + 1 / 10 ^ 4

noncomputable def wideLen (δ : ℝ) : ℝ :=
  1 - wideRho δ

noncomputable def widePref (δ d_r p : ℝ) : ℝ :=
  p * (wideRho δ + d_r)

noncomputable def wideSuf (δ d_r p : ℝ) : ℝ :=
  p * (1 + δ) - widePref δ d_r p

noncomputable def wideDirect (δ d_r p x y : ℝ) : ℝ :=
  crossEntropy (wideRho δ) (widePref δ d_r p) x +
  crossEntropy (wideLen δ) (wideSuf δ d_r p) y

noncomputable def wideNear (δ d_r p x y xi w₁ w₀ : ℝ) : ℝ :=
  wideDirect δ d_r p x y +
  crossEntropy (wideSuf δ d_r p) (xi * wideLen δ / 2) w₁ +
  crossEntropy (wideLen δ - wideSuf δ d_r p) (xi * wideLen δ / 2) w₀ +
  max 0 (wideRho δ + d_r - 508 / 1000) + 1 / 10 ^ 7

noncomputable def wideFar (δ d_r p x xi q : ℝ) : ℝ :=
  2 * crossEntropy (wideRho δ) (widePref δ d_r p) x +
  xi * wideLen δ +
  crossEntropy (wideLen δ - xi * wideLen δ) (wideSuf δ d_r p - xi * wideLen δ / 2) q

noncomputable def wideMenu (δ p z₂ : ℝ) : ℝ :=
  crossEntropy (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂

/-! ## 2. Pure-`Nat` Verification of `logTable512` -/

def logLo (k : ℕ) : ℕ :=
  (logTable512.getD k (0, 0, 0)).2.1

def logHi (k : ℕ) : ℕ :=
  (logTable512.getD k (0, 0, 0)).2.2

def checkLogEntry512 (k : ℕ) : Bool :=
  let sh := (logTable512.getD k (0, 0, 0)).1
  let lo := logLo k
  let hi := logHi k
  let a := 512
  let b := k * 2 ^ sh
  decide (0 < k ∧ b ≤ a ∧ sh * 10 ^ 6 ≤ lo ∧ sh * 10 ^ 6 ≤ hi ∧
    (lo - sh * 10 ^ 6) * atanh5Den (a + b) * 693147181 ≤
      atanh5LowerNum (a - b) (a + b) * 10 ^ 15 ∧
    atanh5UpperNum (a - b) (a + b) * 10 ^ 15 ≤
      (hi - sh * 10 ^ 6) * atanh5UpperDen (a - b) (a + b) * 693147180)

def checkLogTableRange : ℕ → Bool
  | 0 => true
  | n + 1 => checkLogEntry512 (n + 1) && checkLogTableRange n

theorem checkLogTable512_ok : checkLogTableRange 511 = true := by
  decide +kernel

private lemma checkLogTableRange_imp :
    ∀ n : ℕ, checkLogTableRange n = true → ∀ k : ℕ, 1 ≤ k → k ≤ n → checkLogEntry512 k = true
  | 0, _, k, hk1, hk0 => by omega
  | n + 1, h, k, hk1, hkn => by
      simp only [checkLogTableRange, Bool.and_eq_true] at h
      by_cases hkeq : k = n + 1
      · subst hkeq; exact h.1
      · exact checkLogTableRange_imp n h.2 k hk1 (by omega)

theorem logTable512_sound {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 512) :
    (logLo k : ℝ) / 10 ^ 6 ≤ -Real.logb 2 ((k : ℝ) / 512) ∧
    -Real.logb 2 ((k : ℝ) / 512) ≤ (logHi k : ℝ) / 10 ^ 6 := by
  have hentry := checkLogTableRange_imp 511 checkLogTable512_ok k hk1 (by omega)
  unfold checkLogEntry512 at hentry
  dsimp only at hentry
  rw [decide_eq_true_eq] at hentry
  obtain ⟨hkpos, hba, hshlo, hshhi, hlo_nat, hhi_nat⟩ := hentry
  have hlo := neg_logb2_ge_of_nat hkpos hba (by decide : 0 < 10 ^ 6) hshlo
    (by simpa [show (10 ^ 6 : ℕ) * 10 ^ 9 = 10 ^ 15 by decide] using hlo_nat)
  have hhi := neg_logb2_le_of_nat hkpos hba (by decide : 0 < 10 ^ 6) hshhi
    (by simpa [show (10 ^ 6 : ℕ) * 10 ^ 9 = 10 ^ 15 by decide] using hhi_nat)
  have h10 : ((10 ^ 6 : ℕ) : ℝ) = (10 : ℝ) ^ 6 := by norm_num
  have h512 : ((512 : ℕ) : ℝ) = (512 : ℝ) := by norm_num
  rw [h10, h512] at hlo hhi
  exact ⟨hlo, hhi⟩

/-! ## 3. Coordinatewise-Convex Upper Envelopes and 8-Corner Lemma -/

/-- Interval-safe cost upper envelope `max (c * lo) (c * hi)`. -/
noncomputable def costEnv (c : ℝ) (k : ℕ) : ℝ :=
  max (c * ((logLo k : ℝ) / 10 ^ 6)) (c * ((logHi k : ℝ) / 10 ^ 6))

/-- Cross-entropy upper envelope for `k / 512`. -/
noncomputable def crossEnv (a j : ℝ) (k : ℕ) : ℝ :=
  costEnv j k + costEnv (a - j) (512 - k)

noncomputable def directEnv (δ d_r p : ℝ) (xk yk : ℕ) : ℝ :=
  crossEnv (wideRho δ) (widePref δ d_r p) xk +
  crossEnv (wideLen δ) (wideSuf δ d_r p) yk

noncomputable def nearMenuEnv (δ d_r p : ℝ) (xk yk xik w1k w0k z2k : ℕ) : ℝ :=
  directEnv δ d_r p xk yk +
  crossEnv (wideSuf δ d_r p) ((xik : ℝ) / 512 * wideLen δ / 2) w1k +
  crossEnv (wideLen δ - wideSuf δ d_r p) ((xik : ℝ) / 512 * wideLen δ / 2) w0k +
  max 0 (wideRho δ + d_r - 508 / 1000) + 1 / 10 ^ 7 +
  crossEnv (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z2k

noncomputable def farMenuEnv (δ d_r p : ℝ) (xk xik qk z2k : ℕ) : ℝ :=
  2 * crossEnv (wideRho δ) (widePref δ d_r p) xk +
  (xik : ℝ) / 512 * wideLen δ +
  crossEnv (wideLen δ - (xik : ℝ) / 512 * wideLen δ)
    (wideSuf δ d_r p - (xik : ℝ) / 512 * wideLen δ / 2) qk +
  crossEnv (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z2k

private lemma crossEntropy_le_crossEnv (a j : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 512) :
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

/-- A function `φ : ℝ → ℝ` is affine-convex if `φ ((1 - t) a + t b) ≤ (1 - t) φ a + t φ b`
for all `a, b : ℝ` and `t ∈ [0, 1]`. -/
def IsConvexR (φ : ℝ → ℝ) : Prop :=
  ∀ a b t : ℝ, 0 ≤ t → t ≤ 1 → φ ((1 - t) * a + t * b) ≤ (1 - t) * φ a + t * φ b

private lemma isConvexR_const (c : ℝ) : IsConvexR (fun _ => c) := by
  intro a b t _ _; linarith

private lemma isConvexR_affine (m c : ℝ) : IsConvexR (fun x => m * x + c) := by
  intro a b t _ _; linarith

private lemma isConvexR_add {φ ψ : ℝ → ℝ} (h1 : IsConvexR φ) (h2 : IsConvexR ψ) :
    IsConvexR (fun x => φ x + ψ x) := by
  intro a b t ht0 ht1
  linarith [h1 a b t ht0 ht1, h2 a b t ht0 ht1]

private lemma isConvexR_const_mul {c : ℝ} (hc : 0 ≤ c) {φ : ℝ → ℝ} (h : IsConvexR φ) :
    IsConvexR (fun x => c * φ x) := by
  intro a b t ht0 ht1
  have := mul_le_mul_of_nonneg_left (h a b t ht0 ht1) hc
  linarith

private lemma isConvexR_max {φ ψ : ℝ → ℝ} (h1 : IsConvexR φ) (h2 : IsConvexR ψ) :
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

private lemma isConvexR_costEnv_affine (m c : ℝ) (k : ℕ) :
    IsConvexR (fun x => costEnv (m * x + c) k) := by
  unfold costEnv
  apply isConvexR_max
  · have h := isConvexR_affine (m * ((logLo k : ℝ) / 10 ^ 6)) (c * ((logLo k : ℝ) / 10 ^ 6))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith
  · have h := isConvexR_affine (m * ((logHi k : ℝ) / 10 ^ 6)) (c * ((logHi k : ℝ) / 10 ^ 6))
    intro a b t ht0 ht1; have := h a b t ht0 ht1; linarith

private lemma isConvexR_crossEnv_affine (m₁ c₁ m₂ c₂ : ℝ) (k : ℕ) :
    IsConvexR (fun x => crossEnv (m₁ * x + c₁) (m₂ * x + c₂) k) := by
  unfold crossEnv
  apply isConvexR_add
  · exact isConvexR_costEnv_affine m₂ c₂ k
  · have h := isConvexR_costEnv_affine (m₁ - m₂) (c₁ - c₂) (512 - k)
    intro a b t ht0 ht1
    have := h a b t ht0 ht1
    have heq : ∀ y : ℝ, (m₁ - m₂) * y + (c₁ - c₂) = m₁ * y + c₁ - (m₂ * y + c₂) := fun y => by ring
    simpa [heq] using this

/-- Endpoint maximum lemma for `IsConvexR` on `[a, b]`. -/
private lemma isConvexR_lt_of_endpoints {φ : ℝ → ℝ} (h : IsConvexR φ) {a b x T : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (ha : φ a < T) (hb : φ b < T) : φ x < T := by
  by_cases hab : a = b
  · have hxa : x = a := by linarith
    rwa [hxa]
  · have hlt : a < b := lt_of_le_of_ne (hax.trans hxb) hab
    set t := (x - a) / (b - a)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hx : x = (1 - t) * a + t * b := by dsimp [t]; field_simp [(sub_ne_zero.mpr hlt.ne')]; ring
    have hcx := h a b t ht0 ht1
    rw [← hx] at hcx
    have hcomb : (1 - t) * φ a + t * φ b < (1 - t) * T + t * T := by
      by_cases ht0' : t = 0
      · rw [ht0']; linarith
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
        have h1 : (1 - t) * φ a ≤ (1 - t) * T := mul_le_mul_of_nonneg_left ha.le (by linarith)
        have h2 : t * φ b < t * T := mul_lt_mul_of_pos_left hb htpos
        linarith
    linarith

/-- **8-Corner Theorem for Coordinatewise-Convex Functions:**
If `Φ` is convex in each of its three coordinates separately, then `Φ < T` at all 8 corners
of `[d₀, d₁] × [e₀, e₁] × [p₀, p₁]` implies `Φ δ d_r p < T` everywhere on the box. -/
theorem coordConvex_lt_of_corners {Φ : ℝ → ℝ → ℝ → ℝ}
    (hD : ∀ e p, IsConvexR (fun d => Φ d e p))
    (hE : ∀ d p, IsConvexR (fun e => Φ d e p))
    (hP : ∀ d e, IsConvexR (fun p => Φ d e p))
    {d₀ d₁ e₀ e₁ p₀ p₁ δ d_r p T : ℝ}
    (hd : d₀ ≤ δ ∧ δ ≤ d₁) (he : e₀ ≤ d_r ∧ d_r ≤ e₁) (hp : p₀ ≤ p ∧ p ≤ p₁)
    (h000 : Φ d₀ e₀ p₀ < T) (h001 : Φ d₀ e₀ p₁ < T)
    (h010 : Φ d₀ e₁ p₀ < T) (h011 : Φ d₀ e₁ p₁ < T)
    (h100 : Φ d₁ e₀ p₀ < T) (h101 : Φ d₁ e₀ p₁ < T)
    (h110 : Φ d₁ e₁ p₀ < T) (h111 : Φ d₁ e₁ p₁ < T) :
    Φ δ d_r p < T := by
  have hp00 : Φ d₀ e₀ p < T := isConvexR_lt_of_endpoints (hP d₀ e₀) hp.1 hp.2 h000 h001
  have hp01 : Φ d₀ e₁ p < T := isConvexR_lt_of_endpoints (hP d₀ e₁) hp.1 hp.2 h010 h011
  have hp10 : Φ d₁ e₀ p < T := isConvexR_lt_of_endpoints (hP d₁ e₀) hp.1 hp.2 h100 h101
  have hp11 : Φ d₁ e₁ p < T := isConvexR_lt_of_endpoints (hP d₁ e₁) hp.1 hp.2 h110 h111
  have he0 : Φ d₀ d_r p < T := isConvexR_lt_of_endpoints (hE d₀ p) he.1 he.2 hp00 hp01
  have he1 : Φ d₁ d_r p < T := isConvexR_lt_of_endpoints (hE d₁ p) he.1 he.2 hp10 hp11
  exact isConvexR_lt_of_endpoints (hD d_r p) hd.1 hd.2 he0 he1

private lemma isConvexR_congr {φ ψ : ℝ → ℝ} (h : IsConvexR φ) (heq : ∀ x, φ x = ψ x) :
    IsConvexR ψ := by
  intro a b t ht0 ht1
  rw [← heq, ← heq, ← heq]
  exact h a b t ht0 ht1

-- Coordinatewise convexity of directEnv, nearMenuEnv, farMenuEnv:
private lemma directEnv_convex_d (e p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun d => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)
        p (p * (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) xk) (fun x => ?_)
    unfold widePref wideRho; congr 1 <;> ring
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine (-1) (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4))
        0 (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e))) yk) (fun x => ?_)
    unfold wideLen wideSuf widePref wideRho; congr 1 <;> ring

private lemma directEnv_convex_e (d p : ℝ) (xk yk : ℕ) :
    IsConvexR (fun e => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (wideRho d) p (p * wideRho d) xk) (fun x => ?_)
    unfold widePref; congr 1 <;> ring
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (wideLen d) (-p) (p * (1 + d) - p * wideRho d) yk) (fun x => ?_)
    unfold wideSuf widePref; congr 1 <;> ring

private lemma directEnv_convex_p (d e : ℝ) (xk yk : ℕ) :
    IsConvexR (fun p => directEnv d e p xk yk) := by
  unfold directEnv
  apply isConvexR_add
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (wideRho d) (wideRho d + e) 0 xk) (fun x => ?_)
    unfold widePref; congr 1 <;> ring
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (wideLen d) (1 + d - (wideRho d + e)) 0 yk) (fun x => ?_)
    unfold wideSuf widePref; congr 1 <;> ring

private lemma nearMenuEnv_convex_d (e p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun d => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_add
        · apply isConvexR_add
          · exact directEnv_convex_d e p xk yk
          · refine isConvexR_congr
              (isConvexR_crossEnv_affine 0 (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)))
                (-((xik : ℝ) / 512 / 2))
                ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) w1k)
              (fun x => ?_)
            unfold wideSuf widePref wideLen wideRho; congr 1 <;> ring
        · refine isConvexR_congr
            (isConvexR_crossEnv_affine (-1)
              (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4) -
                p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)))
              (-((xik : ℝ) / 512 / 2))
              ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) w0k)
            (fun x => ?_)
          unfold wideLen wideSuf widePref wideRho; congr 1 <;> ring
      · apply isConvexR_max (isConvexR_const 0)
        refine isConvexR_congr
          (isConvexR_affine 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e - 508 / 1000))
          (fun x => by unfold wideRho; ring)
    · exact isConvexR_const (1 / 10 ^ 7)
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma nearMenuEnv_convex_e (d p : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun e => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_add
        · apply isConvexR_add
          · exact directEnv_convex_e d p xk yk
          · refine isConvexR_congr
              (isConvexR_crossEnv_affine (-p) (p * (1 + d) - p * wideRho d)
                0 ((xik : ℝ) / 512 * wideLen d / 2) w1k) (fun x => ?_)
            unfold wideSuf widePref; congr 1 <;> ring
        · refine isConvexR_congr
            (isConvexR_crossEnv_affine p (wideLen d - (p * (1 + d) - p * wideRho d))
              0 ((xik : ℝ) / 512 * wideLen d / 2) w0k) (fun x => ?_)
          unfold wideSuf widePref; congr 1 <;> ring
      · apply isConvexR_max (isConvexR_const 0)
        refine isConvexR_congr (isConvexR_affine 1 (wideRho d - 508 / 1000)) (fun _ => by ring)
    · exact isConvexR_const (1 / 10 ^ 7)
  · exact isConvexR_const _

private lemma nearMenuEnv_convex_p (d e : ℝ) (xk yk xik w1k w0k z2k : ℕ) :
    IsConvexR (fun p => nearMenuEnv d e p xk yk xik w1k w0k z2k) := by
  unfold nearMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_add
        · apply isConvexR_add
          · exact directEnv_convex_p d e xk yk
          · refine isConvexR_congr
              (isConvexR_crossEnv_affine (1 + d - (wideRho d + e)) 0
                0 ((xik : ℝ) / 512 * wideLen d / 2) w1k) (fun x => ?_)
            unfold wideSuf widePref; congr 1 <;> ring
        · refine isConvexR_congr
            (isConvexR_crossEnv_affine (-(1 + d - (wideRho d + e))) (wideLen d)
              0 ((xik : ℝ) / 512 * wideLen d / 2) w0k) (fun x => ?_)
          unfold wideSuf widePref; congr 1 <;> ring
      · exact isConvexR_const _
    · exact isConvexR_const (1 / 10 ^ 7)
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma farMenuEnv_convex_d (e p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun d => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_const_mul (by norm_num)
        refine isConvexR_congr
          (isConvexR_crossEnv_affine 1 (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)
            p (p * (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) xk) (fun x => ?_)
        unfold widePref wideRho; congr 1 <;> ring
      · refine isConvexR_congr
          (isConvexR_affine (-((xik : ℝ) / 512))
            ((xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4))))
          (fun x => by unfold wideLen wideRho; ring)
    · refine isConvexR_congr
        (isConvexR_crossEnv_affine (-(1 - (xik : ℝ) / 512))
          ((1 - (xik : ℝ) / 512) * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)))
          ((xik : ℝ) / 512 / 2)
          (p * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4 + e)) -
            (xik : ℝ) / 512 * (1 - (492 / 1000 + 3 / 10 ^ 7 + 1 / 10 ^ 4)) / 2) qk)
        (fun x => ?_)
      unfold wideSuf widePref wideLen wideRho; congr 1 <;> ring
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (508 / 1000)
        (-p) (p * (508 / 1000 - (1 / 10 ^ 7) * (1508 / 1000))) z2k) (fun x => ?_)
    congr 1 <;> ring

private lemma farMenuEnv_convex_e (d p : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun e => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_const_mul (by norm_num)
        refine isConvexR_congr
          (isConvexR_crossEnv_affine 0 (wideRho d) p (p * wideRho d) xk) (fun x => ?_)
        unfold widePref; congr 1 <;> ring
      · exact isConvexR_const _
    · refine isConvexR_congr
        (isConvexR_crossEnv_affine 0 (wideLen d - (xik : ℝ) / 512 * wideLen d)
          (-p) (p * (1 + d) - p * wideRho d - (xik : ℝ) / 512 * wideLen d / 2) qk) (fun x => ?_)
      unfold wideSuf widePref; congr 1 <;> ring
  · exact isConvexR_const _

private lemma farMenuEnv_convex_p (d e : ℝ) (xk xik qk z2k : ℕ) :
    IsConvexR (fun p => farMenuEnv d e p xk xik qk z2k) := by
  unfold farMenuEnv
  apply isConvexR_add
  · apply isConvexR_add
    · apply isConvexR_add
      · apply isConvexR_const_mul (by norm_num)
        refine isConvexR_congr
          (isConvexR_crossEnv_affine 0 (wideRho d) (wideRho d + e) 0 xk) (fun x => ?_)
        unfold widePref; congr 1 <;> ring
      · exact isConvexR_const _
    · refine isConvexR_congr
        (isConvexR_crossEnv_affine 0 (wideLen d - (xik : ℝ) / 512 * wideLen d)
          (1 + d - (wideRho d + e)) (-((xik : ℝ) / 512 * wideLen d / 2)) qk) (fun x => ?_)
      unfold wideSuf widePref; congr 1 <;> ring
  · refine isConvexR_congr
      (isConvexR_crossEnv_affine 0 (508 / 1000)
        (508 / 1000 - d - (1 / 10 ^ 7) * (1508 / 1000)) 0 z2k) (fun x => ?_)
    congr 1 <;> ring

/-! ## 4. Pure-`Int` BSP Checker and Full Kernel Verification -/

def dCoord : ℤ := 10 ^ 10 * 2 ^ 14
def dTot : ℤ := dCoord * 10 ^ 8 * 1024 * 10 ^ 6

def costInt (cS : ℤ) (k : ℕ) : ℤ :=
  max (cS * (logLo k : ℤ)) (cS * (logHi k : ℤ))

def crossInt (lenS onesS : ℤ) (k : ℕ) : ℤ :=
  costInt onesS k + costInt (lenS - onesS) (512 - k)

def checkCornerInt (dI eI pI : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ) : Bool :=
  let rhoI : ℤ := 4921003000 * 2 ^ 14 + dI
  let lenI : ℤ := dCoord - rhoI
  let rhoS : ℤ := 1024 * 10 ^ 8 * rhoI
  let lenS : ℤ := 1024 * 10 ^ 8 * lenI
  let prefS : ℤ := 1024 * pI * (rhoI + eI)
  let sufS : ℤ := 1024 * pI * (dCoord + dI) - prefS
  let firstInt : ℤ := crossInt rhoS prefS xk
  let directInt : ℤ := firstInt + crossInt lenS sufS yk
  if !useColl then
    decide (10000 * directInt < 9449 * dTot)
  else
    let halfDistS : ℤ := (xik : ℤ) * 10 ^ 8 * lenI
    let distS : ℤ := 2 * halfDistS
    let betaS : ℤ := 1024 * 10 ^ 8 * (5080000000 * 2 ^ 14)
    let menuOnesS : ℤ := 1024 * pI * (5080000000 * 2 ^ 14 - dI - 1508 * 2 ^ 14)
    let recovInt : ℤ :=
      max 0 (rhoI + eI - 5080000000 * 2 ^ 14) * (1024 * 10 ^ 8 * 10 ^ 6) +
      (10 ^ 3 * 2 ^ 14) * (1024 * 10 ^ 8 * 10 ^ 6)
    let nearInt : ℤ :=
      directInt + crossInt sufS halfDistS w1k + crossInt (lenS - sufS) halfDistS w0k + recovInt
    let farInt : ℤ :=
      2 * firstInt + distS * 10 ^ 6 + crossInt (lenS - distS) (sufS - halfDistS) qk
    let menuInt : ℤ := crossInt betaS menuOnesS z2k
    decide (10000 * (nearInt + menuInt) < 2 * 9449 * dTot ∧
      10000 * (farInt + menuInt) < 2 * 9449 * dTot)

def checkLeafInt (d0 d1 e0 e1 : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ) : Bool :=
  decide (1 ≤ xk ∧ xk < 512 ∧ 1 ≤ yk ∧ yk < 512 ∧ 1 ≤ xik ∧ xik < 512 ∧
    1 ≤ w1k ∧ w1k < 512 ∧ 1 ≤ w0k ∧ w0k < 512 ∧ w1k + w0k ≤ 512 ∧
    1 ≤ qk ∧ qk < 512 ∧ 256 ≤ z2k ∧ z2k < 512) &&
  checkCornerInt d0 e0 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d0 e0 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d0 e1 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d0 e1 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d1 e0 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d1 e0 63092976 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d1 e1 63092975 useColl xk yk xik w1k w0k qk z2k &&
  checkCornerInt d1 e1 63092976 useColl xk yk xik w1k w0k qk z2k

def checkBSP (d0 d1 e0 e1 : ℤ) : BSPTree → Bool
  | .leaf useColl xk yk xik w1k w0k qk z2k =>
      checkLeafInt d0 d1 e0 e1 useColl xk yk xik w1k w0k qk z2k
  | .splitD l r =>
      let mid := (d0 + d1) / 2
      decide (2 * mid = d0 + d1) && checkBSP d0 mid e0 e1 l && checkBSP mid d1 e0 e1 r
  | .splitE l r =>
      let mid := (e0 + e1) / 2
      decide (2 * mid = e0 + e1) && checkBSP d0 d1 e0 mid l && checkBSP d0 d1 mid e1 r

/-- **Pure-Kernel Verification of All 202 Wide-Slack BSP Rectangles (`decide +kernel`, ZERO `native_decide`):** -/
theorem wideSlackBSP_ok :
    checkBSP (-10 ^ 3 * 2 ^ 14) (12 * 10 ^ 7 * 2 ^ 14)
      (-10 ^ 3 * 2 ^ 14) (10 ^ 10 * 2 ^ 14) wideSlackBSP = true := by
  decide +kernel

private lemma max_div_pos {a b c : ℝ} (hc : 0 < c) : max a b / c = max (a / c) (b / c) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hc.le)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (div_le_div_of_nonneg_right h' hc.le)]

private lemma costInt_cast (cS : ℤ) (k : ℕ) :
    (costInt cS k : ℝ) / (dTot : ℝ) = costEnv ((cS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024)) k := by
  unfold costInt costEnv
  have hd_pos : (0 : ℝ) < (dTot : ℝ) := by unfold dTot dCoord; positivity
  have hcast : ((max (cS * (logLo k : ℤ)) (cS * (logHi k : ℤ)) : ℤ) : ℝ) =
      max ((cS : ℝ) * (logLo k : ℝ)) ((cS : ℝ) * (logHi k : ℝ)) := by push_cast; rfl
  rw [hcast, max_div_pos hd_pos]
  unfold dTot
  push_cast
  congr 1 <;> ring

private lemma crossInt_cast (lenS onesS : ℤ) (k : ℕ) :
    (crossInt lenS onesS k : ℝ) / (dTot : ℝ) =
      crossEnv ((lenS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024))
        ((onesS : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024)) k := by
  unfold crossInt crossEnv
  push_cast
  rw [add_div, costInt_cast, costInt_cast]
  congr 2
  push_cast
  ring

private lemma checkCornerInt_sound (dI eI pI : ℤ) (useColl : Bool) (xk yk xik w1k w0k qk z2k : ℕ)
    (hok : checkCornerInt dI eI pI useColl xk yk xik w1k w0k qk z2k = true) :
    let d : ℝ := (dI : ℝ) / (dCoord : ℝ)
    let e : ℝ := (eI : ℝ) / (dCoord : ℝ)
    let p : ℝ := (pI : ℝ) / 10 ^ 8
    (useColl = false → directEnv d e p xk yk < 9449 / 10000) ∧
    (useColl = true →
      nearMenuEnv d e p xk yk xik w1k w0k z2k < 2 * (9449 / 10000) ∧
      farMenuEnv d e p xk xik qk z2k < 2 * (9449 / 10000)) := by
  intro d e p
  have hdC : (dCoord : ℝ) ≠ 0 := by unfold dCoord; positivity
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
    push_cast; rw [add_div, crossInt_cast, crossInt_cast, hrho, hlen, hpref, hsuf]
    rfl
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
        rw [ht1, ht2, max_div_pos hdC_pos, zero_div]
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
        simp only [add_div, crossInt_cast, hrecov, hrho, hlen, hpref, hsuf, hhalf, hbeta, hmenuOnes]
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
        simp only [add_div, crossInt_cast, hbeta, hmenuOnes]
        have hsub1 : ((lenS - distS : ℤ) : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
            wideLen d - (xik : ℝ) / 512 * wideLen d := by
          rw [Int.cast_sub, sub_div, hlen, hdist]
        have hsub2 : ((sufS - halfDistS : ℤ) : ℝ) / ((dCoord : ℝ) * 10 ^ 8 * 1024) =
            wideSuf d e p - (xik : ℝ) / 512 * wideLen d / 2 := by
          rw [Int.cast_sub, sub_div, hsuf, hhalf]
        have htwo : 2 * (crossInt rhoS prefS xk : ℝ) / (dTot : ℝ) =
            2 * crossEnv (wideRho d) (widePref d e p) xk := by
          rw [mul_div_assoc, crossInt_cast, hrho, hpref]
        have hdist_term : (distS : ℝ) * 1000000 / (dTot : ℝ) =
            (xik : ℝ) / 512 * wideLen d := by
          rw [← hdist]; unfold dTot; push_cast; ring
        rw [htwo, hsub1, hsub2, hdist_term]
      constructor
      · have h1 : (10000 : ℝ) * (nearTotal : ℝ) < (2 * 9449 : ℝ) * (dTot : ℝ) := by
          have h1' : ((10000 * nearTotal : ℤ) : ℝ) < ((2 * 9449 * dTot : ℤ) : ℝ) := by
            exact_mod_cast hok.1
          push_cast at h1'; linarith only [h1']
        rw [← hnear_eq, div_lt_iff₀ hdTot_pos]
        linarith only [h1]
      · have h2 : (10000 : ℝ) * (farTotal : ℝ) < (2 * 9449 : ℝ) * (dTot : ℝ) := by
          have h2' : ((10000 * farTotal : ℤ) : ℝ) < ((2 * 9449 * dTot : ℤ) : ℝ) := by
            exact_mod_cast hok.2
          push_cast at h2'; linarith only [h2']
        rw [← hfar_eq, div_lt_iff₀ hdTot_pos]
        linarith only [h2]

private lemma checkBSP_sound (tree : BSPTree) :
    ∀ d0 d1 e0 e1 : ℤ, checkBSP d0 d1 e0 e1 tree = true →
    ∀ δ d_r p : ℝ,
      (d0 : ℝ) / (dCoord : ℝ) ≤ δ ∧ δ ≤ (d1 : ℝ) / (dCoord : ℝ) →
      (e0 : ℝ) / (dCoord : ℝ) ≤ d_r ∧ d_r ≤ (e1 : ℝ) / (dCoord : ℝ) →
      (63092975 : ℝ) / 10 ^ 8 ≤ p ∧ p ≤ (63092976 : ℝ) / 10 ^ 8 →
      ∃ x y xi w₁ w₀ q z₂ : ℝ,
        0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧ 0 < xi ∧ xi < 1 ∧
        0 < w₁ ∧ w₁ < 1 ∧ 0 < w₀ ∧ w₀ < 1 ∧ w₁ + w₀ ≤ 1 ∧
        0 < q ∧ q < 1 ∧ (1 : ℝ) / 2 ≤ z₂ ∧ z₂ < 1 ∧
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
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hx2,
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hy2,
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hxi2,
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hw12,
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hw02,
        by rw [← add_div, div_le_one (by norm_num)]; exact_mod_cast hwsum,
        by positivity, by rw [div_lt_one (by norm_num)]; exact_mod_cast hq2,
        by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; exact_mod_cast (by omega : 512 ≤ z2k * 2),
        by rw [div_lt_one (by norm_num)]; exact_mod_cast hz22, ?_⟩
      have h000 := checkCornerInt_sound d0 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc000
      have h001 := checkCornerInt_sound d0 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc001
      have h010 := checkCornerInt_sound d0 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc010
      have h011 := checkCornerInt_sound d0 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc011
      have h100 := checkCornerInt_sound d1 e0 63092975 useColl xk yk xik w1k w0k qk z2k hc100
      have h101 := checkCornerInt_sound d1 e0 63092976 useColl xk yk xik w1k w0k qk z2k hc101
      have h110 := checkCornerInt_sound d1 e1 63092975 useColl xk yk xik w1k w0k qk z2k hc110
      have h111 := checkCornerInt_sound d1 e1 63092976 useColl xk yk xik w1k w0k qk z2k hc111
      cases useColl
      · apply lt_of_le_of_lt (min_le_left _ _)
        have hdir_le : wideDirect δ d_r p ((xk : ℝ) / 512) ((yk : ℝ) / 512) ≤
            directEnv δ d_r p xk yk := by
          unfold wideDirect directEnv
          exact add_le_add (crossEntropy_le_crossEnv _ _ hx1 hx2)
            (crossEntropy_le_crossEnv _ _ hy1 hy2)
        have henv : directEnv δ d_r p xk yk < 9449 / 10000 :=
          coordConvex_lt_of_corners
            (fun e' p' => directEnv_convex_d e' p' xk yk)
            (fun d' p' => directEnv_convex_e d' p' xk yk)
            (fun d' e' => directEnv_convex_p d' e' xk yk)
            hd he hp
            (h000.1 rfl) (h001.1 rfl) (h010.1 rfl) (h011.1 rfl)
            (h100.1 rfl) (h101.1 rfl) (h110.1 rfl) (h111.1 rfl)
        exact lt_of_le_of_lt hdir_le henv
      · apply lt_of_le_of_lt (min_le_right _ _)
        have hnear_le : wideNear δ d_r p ((xk : ℝ) / 512) ((yk : ℝ) / 512) ((xik : ℝ) / 512)
            ((w1k : ℝ) / 512) ((w0k : ℝ) / 512) + wideMenu δ p ((z2k : ℝ) / 512) ≤
            nearMenuEnv δ d_r p xk yk xik w1k w0k z2k := by
          unfold wideNear wideDirect wideMenu nearMenuEnv directEnv
          have h1 := crossEntropy_le_crossEnv (wideRho δ) (widePref δ d_r p) hx1 hx2
          have h2 := crossEntropy_le_crossEnv (wideLen δ) (wideSuf δ d_r p) hy1 hy2
          have h3 := crossEntropy_le_crossEnv (wideSuf δ d_r p) ((xik : ℝ) / 512 * wideLen δ / 2) hw11 hw12
          have h4 := crossEntropy_le_crossEnv (wideLen δ - wideSuf δ d_r p)
            ((xik : ℝ) / 512 * wideLen δ / 2) hw01 hw02
          have h5 := crossEntropy_le_crossEnv (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22
          linarith
        have hfar_le : wideFar δ d_r p ((xk : ℝ) / 512) ((xik : ℝ) / 512) ((qk : ℝ) / 512) +
            wideMenu δ p ((z2k : ℝ) / 512) ≤ farMenuEnv δ d_r p xk xik qk z2k := by
          unfold wideFar wideMenu farMenuEnv
          have h1 := crossEntropy_le_crossEnv (wideRho δ) (widePref δ d_r p) hx1 hx2
          have h2 := crossEntropy_le_crossEnv (wideLen δ - (xik : ℝ) / 512 * wideLen δ)
            (wideSuf δ d_r p - (xik : ℝ) / 512 * wideLen δ / 2) hq1 hq2
          have h3 := crossEntropy_le_crossEnv (508 / 1000)
            (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) (by omega : 1 ≤ z2k) hz22
          linarith
        have hnear_lt : nearMenuEnv δ d_r p xk yk xik w1k w0k z2k < 2 * (9449 / 10000) :=
          coordConvex_lt_of_corners
            (fun e' p' => nearMenuEnv_convex_d e' p' xk yk xik w1k w0k z2k)
            (fun d' p' => nearMenuEnv_convex_e d' p' xk yk xik w1k w0k z2k)
            (fun d' e' => nearMenuEnv_convex_p d' e' xk yk xik w1k w0k z2k)
            hd he hp
            (h000.2 rfl).1 (h001.2 rfl).1 (h010.2 rfl).1 (h011.2 rfl).1
            (h100.2 rfl).1 (h101.2 rfl).1 (h110.2 rfl).1 (h111.2 rfl).1
        have hfar_lt : farMenuEnv δ d_r p xk xik qk z2k < 2 * (9449 / 10000) :=
          coordConvex_lt_of_corners
            (fun e' p' => farMenuEnv_convex_d e' p' xk xik qk z2k)
            (fun d' p' => farMenuEnv_convex_e d' p' xk xik qk z2k)
            (fun d' e' => farMenuEnv_convex_p d' e' xk xik qk z2k)
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

/-- **Complete Pure-Kernel Wide-Slack `0.055` (`< 0.9449`) Uniform Certificate Theorem:**
For EVERY `(δ, d_r) ∈ [-10^{-7}, 0.012] × [-10^{-7}, 1]` and `p = log_3 2`, there exist valid
tilts `x, y, xi, w₁, w₀, q, z₂ ∈ (0, 1)` (`w₁ + w₀ ≤ 1`, `1/2 ≤ z₂`) certifying
`min(U, max((N + M_2)/2, (F + M_2)/2)) < 9449 / 10000` (giving `> 10^{-4}` margin below `0.945`). -/
theorem wide_slack_0055_uniform_bound (δ d_r : ℝ)
    (hδ : -(1 / 10 ^ 7 : ℝ) ≤ δ ∧ δ ≤ 12 / 1000)
    (hd_r : -(1 / 10 ^ 7 : ℝ) ≤ d_r ∧ d_r ≤ 1) :
    let p := Real.log 2 / Real.log 3
    ∃ x y xi w₁ w₀ q z₂ : ℝ,
      0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧ 0 < xi ∧ xi < 1 ∧
      0 < w₁ ∧ w₁ < 1 ∧ 0 < w₀ ∧ w₀ < 1 ∧ w₁ + w₀ ≤ 1 ∧
      0 < q ∧ q < 1 ∧ (1 : ℝ) / 2 ≤ z₂ ∧ z₂ < 1 ∧
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
  exact checkBSP_sound wideSlackBSP
    (-10 ^ 3 * 2 ^ 14) (12 * 10 ^ 7 * 2 ^ 14)
    (-10 ^ 3 * 2 ^ 14) (10 ^ 10 * 2 ^ 14)
    wideSlackBSP_ok δ d_r p hd_cast he_cast ⟨hp.1.le, hp.2.le⟩

end CollatzTwoWindow
