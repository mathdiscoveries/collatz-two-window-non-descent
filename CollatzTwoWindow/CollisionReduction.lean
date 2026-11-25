module

public import CollatzTwoWindow.ShortcutCoding
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Tactic

/-!
# Two-Window Collision Reduction, Wrap-Separation, and Cumulative Stopping-Time Bounds

Formalizes the combinatorial, algebraic, and Diophantine-interface reductions of the
classical two-window stopping-time theorem:

1. **Cauchy–Schwarz collision and slice inequalities:**
   - `collisionCount_eq_sum_fiber_sq`, `card_sq_le_card_mul_collisions` (`|A|^2 ≤ |S| C`),
     and `collisionCount_biUnion_le` (`C(⋃_i A_i) ≤ |I| ∑_i C(A_i)`).
2. **Shift-difference localization and close-pair intermediate uniqueness:**
   - `shift_center_identity`, `shift_center_bound`, `close_pair_intermediate_congr`,
     and `close_pair_intermediate_card_le`.
3. **Algebraic wrap-separation reduction to the 3-place `{∞, 2, 3}` Subspace inequality:**
   - `padicAbs`, `threePlaceProduct`, `primitive_threePlaceProduct_le`,
   - `wrap_separation_vector_bounds`, `wrap_separation_three_place_bound`,
   - and `slope_band_ratio`.
4. **Explicit quantitative Subspace Theorem interface and cumulative `N_T(X)` bounds:**
   - `ThreePlaceSubspaceHypothesis` (explicit structure — never a silent axiom) and
     `subspace_implies_exceptional_bands`.
   - `ShellSeparationCovering`, `cumulative_count_outside_bands` (`N_T(X) ≤ 5 X^a`),
     `good_scale_in_window` (`∃ x ∈ [X_1, X_1^{3.2^{R+1}}]`), and
     `eventual_bound_of_shell_covering` (`∃ C, ∀ X ≥ 1, N_T(X) ≤ C X^a`).
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Cauchy–Schwarz Two-Window Collision & Slice Inequalities -/

/-- Ordered collision count of `f` on a finite set `A`:
`#{(a, b) ∈ A × A : f a = f b}`. -/
def collisionCount {α β : Type*} [DecidableEq β] (A : Finset α) (f : α → β) : ℕ :=
  ((A ×ˢ A).filter (fun p => f p.1 = f p.2)).card

/-- Finite-sum Cauchy–Schwarz in `ℕ`: `(∑ i ∈ S, c i)^2 ≤ S.card * ∑ i ∈ S, (c i)^2`. -/
theorem nat_sq_sum_le_card_mul_sum_sq {ι : Type*} (S : Finset ι) (c : ι → ℕ) :
    (∑ i ∈ S, c i) ^ 2 ≤ S.card * ∑ i ∈ S, c i ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ ∑ i ∈ S, ∑ j ∈ S, ((c i : ℤ) - (c j : ℤ)) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg _
  have hexpand :
      (∑ i ∈ S, ∑ j ∈ S, ((c i : ℤ) - (c j : ℤ)) ^ 2) =
        2 * (S.card : ℤ) * (∑ i ∈ S, (c i : ℤ) ^ 2) - 2 * (∑ i ∈ S, (c i : ℤ)) ^ 2 := by
    have h1 : ∀ i ∈ S,
        ∑ j ∈ S, ((c i : ℤ) - (c j : ℤ)) ^ 2 =
          (S.card : ℤ) * (c i : ℤ) ^ 2 - 2 * (c i : ℤ) * (∑ j ∈ S, (c j : ℤ)) +
            ∑ j ∈ S, (c j : ℤ) ^ 2 := by
      intro i _
      calc
        ∑ j ∈ S, ((c i : ℤ) - (c j : ℤ)) ^ 2
          = ∑ j ∈ S, ((c i : ℤ) ^ 2 - 2 * (c i : ℤ) * (c j : ℤ) + (c j : ℤ) ^ 2) := by
            apply Finset.sum_congr rfl; intro j _; ring
        _ = (∑ _j ∈ S, (c i : ℤ) ^ 2) - (∑ j ∈ S, 2 * (c i : ℤ) * (c j : ℤ)) +
            ∑ j ∈ S, (c j : ℤ) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (S.card : ℤ) * (c i : ℤ) ^ 2 - 2 * (c i : ℤ) * (∑ j ∈ S, (c j : ℤ)) +
            ∑ j ∈ S, (c j : ℤ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hmid : (∑ i ∈ S, 2 * (c i : ℤ) * (∑ j ∈ S, (c j : ℤ))) =
        2 * (∑ i ∈ S, (c i : ℤ)) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sq]
      ring
    rw [hmid]
    ring
  rw [hexpand] at hnonneg
  have hz : (∑ i ∈ S, (c i : ℤ)) ^ 2 ≤ (S.card : ℤ) * (∑ i ∈ S, (c i : ℤ) ^ 2) := by
    linarith
  exact_mod_cast hz

/-- Collision count equals the sum of squared fiber sizes over any codomain `S` containing `f '' A`. -/
theorem collisionCount_eq_sum_fiber_sq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (S : Finset β) (f : α → β) (hf : ∀ a ∈ A, f a ∈ S) :
    collisionCount A f = ∑ y ∈ S, (A.filter (fun a => f a = y)).card ^ 2 := by
  unfold collisionCount
  have hpart :
      (A ×ˢ A).filter (fun p => f p.1 = f p.2) =
        S.biUnion (fun y => (A.filter (fun a => f a = y)) ×ˢ (A.filter (fun a => f a = y))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨ha, hb⟩, hfab⟩
      exact ⟨f a, hf a ha, ⟨ha, rfl⟩, ⟨hb, hfab.symm⟩⟩
    · rintro ⟨y, _, ⟨ha, hfa⟩, ⟨hb, hfb⟩⟩
      exact ⟨⟨ha, hb⟩, hfa.trans hfb.symm⟩
  rw [hpart, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.card_product, sq]
  · intro y₁ _ y₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter] at h1 h2
    exact hne (h1.1.2.symm.trans h2.1.2)

/-- **Exact Cauchy–Schwarz Two-Window Inequality:** `|A|^2 ≤ |S| * C(A, f)`. -/
theorem card_sq_le_card_mul_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (S : Finset β) (f : α → β) (hf : ∀ a ∈ A, f a ∈ S) :
    A.card ^ 2 ≤ S.card * collisionCount A f := by
  rw [collisionCount_eq_sum_fiber_sq A S f hf]
  have hcard : A.card = ∑ y ∈ S, (A.filter (fun a => f a = y)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ha => ⟨f a, hf a ha, ha, rfl⟩, fun ⟨_, _, ha, _⟩ => ha⟩
    · intro y₁ _ y₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  rw [hcard]
  exact nat_sq_sum_le_card_mul_sum_sq S (fun y => (A.filter (fun a => f a = y)).card)

/-- **Slice Cauchy–Schwarz Inequality:** partitioning `A` into `|I|` slices multiplies the
ordered collision count (including all cross-slice collisions) by at most `|I|`. -/
theorem collisionCount_biUnion_le {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (I : Finset ι) (slices : ι → Finset α) (A : Finset α) (f : α → β)
    (hcov : A ⊆ I.biUnion slices) :
    collisionCount A f ≤ I.card * ∑ i ∈ I, collisionCount (slices i) f := by
  set S : Finset β := (I.biUnion slices).image f
  have hfA : ∀ a ∈ A, f a ∈ S := fun a ha => Finset.mem_image_of_mem f (hcov ha)
  have hfS : ∀ i ∈ I, ∀ a ∈ slices i, f a ∈ S := fun i hi a ha =>
    Finset.mem_image_of_mem f (Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
  rw [collisionCount_eq_sum_fiber_sq A S f hfA]
  have hrhs :
      ∑ i ∈ I, collisionCount (slices i) f =
        ∑ y ∈ S, ∑ i ∈ I, ((slices i).filter (fun a => f a = y)).card ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact collisionCount_eq_sum_fiber_sq (slices i) S f (hfS i hi)
  rw [hrhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have hfib : (A.filter (fun a => f a = y)).card ≤
      ∑ i ∈ I, ((slices i).filter (fun a => f a = y)).card := by
    calc
      (A.filter (fun a => f a = y)).card
        ≤ (I.biUnion (fun i => (slices i).filter (fun a => f a = y))).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_biUnion] at ha ⊢
          rcases Finset.mem_biUnion.mp (hcov ha.1) with ⟨i, hi, has⟩
          exact ⟨i, hi, has, ha.2⟩
      _ ≤ ∑ i ∈ I, ((slices i).filter (fun a => f a = y)).card := Finset.card_biUnion_le
  calc
    (A.filter (fun a => f a = y)).card ^ 2
      ≤ (∑ i ∈ I, ((slices i).filter (fun a => f a = y)).card) ^ 2 :=
        Nat.pow_le_pow_left hfib 2
    _ ≤ I.card * ∑ i ∈ I, ((slices i).filter (fun a => f a = y)).card ^ 2 :=
        nat_sq_sum_le_card_mul_sum_sq I (fun i => ((slices i).filter (fun a => f a = y)).card)

/-! ## 2. Shift-Difference Localization & Close-Pair Intermediate Uniqueness -/

/-- Exact affine shift-difference identity on a fixed odd-count slice `s_k(n) = s_k(n') = s`
when `T^[k] n' - T^[k] n = ν * 2^m`. -/
theorem shift_center_identity {k m s n n' : ℕ} {ν : ℤ}
    (hs : oddCount k n = s) (hs' : oddCount k n' = s)
    (hdiff : (T^[k] n' : ℤ) - (T^[k] n : ℤ) = ν * (2 : ℤ) ^ m) :
    (n' : ℝ) - (n : ℝ) =
      (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s -
        ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) / (3 : ℝ) ^ s := by
  have h1 : (2 : ℝ) ^ k * (T^[k] n : ℝ) = (3 : ℝ) ^ s * (n : ℝ) + (affineOffset k n : ℝ) := by
    have := two_pow_mul_iterate k n
    rw [hs] at this
    exact_mod_cast this
  have h2 : (2 : ℝ) ^ k * (T^[k] n' : ℝ) = (3 : ℝ) ^ s * (n' : ℝ) + (affineOffset k n' : ℝ) := by
    have := two_pow_mul_iterate k n'
    rw [hs'] at this
    exact_mod_cast this
  have hd : (T^[k] n' : ℝ) - (T^[k] n : ℝ) = (ν : ℝ) * (2 : ℝ) ^ m := by
    exact_mod_cast hdiff
  have h3ne : (3 : ℝ) ^ s ≠ 0 := by positivity
  have hsub : (3 : ℝ) ^ s * ((n' : ℝ) - (n : ℝ)) =
      (ν : ℝ) * (2 : ℝ) ^ (k + m) - ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) := by
    calc
      (3 : ℝ) ^ s * ((n' : ℝ) - (n : ℝ))
        = (2 : ℝ) ^ k * ((T^[k] n' : ℝ) - (T^[k] n : ℝ)) -
            ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) := by linarith
      _ = (2 : ℝ) ^ k * ((ν : ℝ) * (2 : ℝ) ^ m) -
            ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) := by rw [hd]
      _ = (ν : ℝ) * (2 : ℝ) ^ (k + m) -
            ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) := by rw [pow_add]; ring
  field_simp [h3ne]
  linarith

/-- Localization of the shift `n' - n` within radius `R` of `ν * 2^(k+m) / 3^s`, plus the
corresponding bound on `|ν|` for shell starts `n, n' ∈ [2^k, 2^(k+1))`. -/
theorem shift_center_bound {k m s n n' : ℕ} {ν : ℤ} {R : ℝ}
    (hs : oddCount k n = s) (hs' : oddCount k n' = s)
    (hdiff : (T^[k] n' : ℤ) - (T^[k] n : ℤ) = ν * (2 : ℤ) ^ m)
    (hB : (affineOffset k n : ℝ) / (3 : ℝ) ^ s ≤ R)
    (hB' : (affineOffset k n' : ℝ) / (3 : ℝ) ^ s ≤ R) :
    |(n' : ℝ) - (n : ℝ) - (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R := by
  rw [shift_center_identity hs hs' hdiff]
  have hsub :
      (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s -
          ((affineOffset k n' : ℝ) - (affineOffset k n : ℝ)) / (3 : ℝ) ^ s -
          (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s =
        (affineOffset k n : ℝ) / (3 : ℝ) ^ s - (affineOffset k n' : ℝ) / (3 : ℝ) ^ s := by
    ring
  rw [hsub, abs_le]
  have h0 : 0 ≤ (affineOffset k n : ℝ) / (3 : ℝ) ^ s := by positivity
  have h0' : 0 ≤ (affineOffset k n' : ℝ) / (3 : ℝ) ^ s := by positivity
  constructor <;> linarith

theorem shift_index_bound_of_shell {k m s n n' : ℕ} {ν : ℤ} {R : ℝ}
    (hn1 : 2 ^ k ≤ n) (hn2 : n < 2 ^ (k + 1))
    (hn1' : 2 ^ k ≤ n') (hn2' : n' < 2 ^ (k + 1))
    (hloc : |(n' : ℝ) - (n : ℝ) - (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R) :
    |(ν : ℝ)| ≤ ((2 : ℝ) ^ k + R) * (3 : ℝ) ^ s / (2 : ℝ) ^ (k + m) := by
  have hd : |(n' : ℝ) - (n : ℝ)| ≤ (2 : ℝ) ^ k := by
    have h1 : (2 ^ k : ℝ) ≤ n := by exact_mod_cast hn1
    have h2 : (n : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hn2
    have h1' : (2 ^ k : ℝ) ≤ n' := by exact_mod_cast hn1'
    have h2' : (n' : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hn2'
    have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
    rw [abs_le]
    constructor <;> linarith
  have htri : |(ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ (2 : ℝ) ^ k + R := by
    have h1 : |(ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| - |(n' : ℝ) - (n : ℝ)| ≤
        |(n' : ℝ) - (n : ℝ) - (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| := by
      rw [abs_sub_comm ((n' : ℝ) - (n : ℝ))]
      exact abs_sub_abs_le_abs_sub _ _
    linarith
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (k + m) := by positivity
  have hpos3 : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  rw [abs_div, abs_mul, abs_of_pos hpos2, abs_of_pos hpos3] at htri
  rw [le_div_iff₀ hpos2]
  have hmul := mul_le_mul_of_nonneg_right htri hpos3.le
  rw [div_mul_cancel₀ _ hpos3.ne'] at hmul
  exact hmul

/-- Close-pair suffix inversion: because `gcd(3^j, 2^(L+m)) = 1`, fixing the suffix parity word
`(j, B)` and target residue modulo `2^(L+m)` uniquely determines `T^[r] n'` modulo `2^(L+m)`. -/
theorem close_pair_intermediate_congr {j B L m y₁ y₂ : ℕ}
    (hmod : (3 ^ j * y₁ + B) % 2 ^ (L + m) = (3 ^ j * y₂ + B) % 2 ^ (L + m)) :
    y₁ % 2 ^ (L + m) = y₂ % 2 ^ (L + m) := by
  have hcop : Nat.Coprime (3 ^ j) (2 ^ (L + m)) := by
    have : Nat.Coprime 3 2 := by decide
    exact (this.pow_left j).pow_right (L + m)
  have hmeq : 3 ^ j * y₁ + B ≡ 3 ^ j * y₂ + B [MOD 2 ^ (L + m)] := hmod
  have hcancelB : 3 ^ j * y₁ ≡ 3 ^ j * y₂ [MOD 2 ^ (L + m)] :=
    Nat.ModEq.add_right_cancel' B hmeq
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hcancelB

/-- Number of intermediate integers `y ≤ U` matching a fixed residue class modulo `M > 0`
is at most `U / M + 1` (and at most `1` whenever `U < M`). -/
theorem close_pair_intermediate_card_le (j B L m U yTarget : ℕ) :
    ((Finset.range (U + 1)).filter
      (fun y => (3 ^ j * y + B) % 2 ^ (L + m) = yTarget % 2 ^ (L + m))).card ≤
      U / 2 ^ (L + m) + 1 := by
  set M := 2 ^ (L + m)
  have hM : 0 < M := by positivity
  set S := (Finset.range (U + 1)).filter (fun y => (3 ^ j * y + B) % M = yTarget % M)
  have hsub : S.image (fun y => y / M) ⊆ Finset.range (U / M + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨y, hy, rfl⟩
    rw [Finset.mem_range]
    have hyU : y ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hy).1)
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hyU)
  have hinj : Set.InjOn (fun y => y / M) (S : Set ℕ) := by
    intro y₁ hy₁ y₂ hy₂ hdiv
    dsimp only at hdiv
    have hm1 : (3 ^ j * y₁ + B) % M = yTarget % M := (Finset.mem_filter.mp hy₁).2
    have hm2 : (3 ^ j * y₂ + B) % M = yTarget % M := (Finset.mem_filter.mp hy₂).2
    have hrem : y₁ % M = y₂ % M := close_pair_intermediate_congr (hm1.trans hm2.symm)
    have h1 := Nat.div_add_mod y₁ M
    have h2 := Nat.div_add_mod y₂ M
    rw [hdiv, hrem] at h1
    omega
  calc
    S.card = (S.image (fun y => y / M)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (U / M + 1)).card := Finset.card_le_card hsub
    _ = U / M + 1 := Finset.card_range _

theorem close_pair_intermediate_unique {j B L m U yTarget : ℕ}
    (hU : U < 2 ^ (L + m)) :
    ((Finset.range (U + 1)).filter
      (fun y => (3 ^ j * y + B) % 2 ^ (L + m) = yTarget % 2 ^ (L + m))).card ≤ 1 := by
  have h := close_pair_intermediate_card_le j B L m U yTarget
  have hdiv : U / 2 ^ (L + m) = 0 := Nat.div_eq_of_lt hU
  omega

/-! ## 3. Algebraic Wrap-Separation Reduction to `{∞, 2, 3}` Vectors -/

/-- Normalized `p`-adic absolute value `|x|_p = p^(-v_p(x))` for nonzero `x : ℤ`, and `0` at `0`. -/
noncomputable def padicAbs (p : ℕ) (x : ℤ) : ℝ :=
  if x = 0 then 0 else ((p : ℝ) ^ padicValNat p x.natAbs)⁻¹

/-- The 3-place `{∞, 2, 3}` linear-form product of `(X, Z)`:
`|X - Z| * |Z| * |X * Z|_2 * |X * Z|_3`. -/
noncomputable def threePlaceProduct (X Z : ℤ) : ℝ :=
  |(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)| * padicAbs 2 (X * Z) * padicAbs 3 (X * Z)

theorem padicAbs_nonneg (p : ℕ) (x : ℤ) : 0 ≤ padicAbs p x := by
  unfold padicAbs
  split_ifs <;> positivity

theorem padicAbs_mul {p : ℕ} [Fact p.Prime] (x y : ℤ) :
    padicAbs p (x * y) = padicAbs p x * padicAbs p y := by
  unfold padicAbs
  by_cases hx : x = 0
  · subst hx; simp
  · by_cases hy : y = 0
    · subst hy; simp
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      have hxa : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx
      have hya : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
      simp only [hx, hy, hxy, ↓reduceIte, Int.natAbs_mul]
      rw [padicValNat.mul hxa hya, pow_add, mul_inv]

theorem padicAbs_le_of_pow_dvd {p : ℕ} [Fact p.Prime] {x : ℤ} {e : ℕ}
    (hx : x ≠ 0) (hdvd : (p : ℤ) ^ e ∣ x) :
    padicAbs p x ≤ ((p : ℝ) ^ e)⁻¹ := by
  unfold padicAbs
  simp only [hx, ↓reduceIte]
  have hp_gt1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := (Fact.out : p.Prime).one_lt
    exact_mod_cast this.le
  have hdvd_nat : p ^ e ∣ x.natAbs := by
    have : ((p ^ e : ℕ) : ℤ) ∣ x := by exact_mod_cast hdvd
    exact Int.natCast_dvd.mp this
  have hle : e ≤ padicValNat p x.natAbs :=
    (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hx)).mp hdvd_nat
  have hpow_le : (p : ℝ) ^ e ≤ (p : ℝ) ^ padicValNat p x.natAbs :=
    pow_le_pow_right₀ hp_gt1 hle
  have hpos : (0 : ℝ) < (p : ℝ) ^ e := by
    have := (Fact.out : p.Prime).pos
    positivity
  exact inv_anti₀ hpos hpow_le

theorem nat_mul_padicAbs_two_three_ge_one {g : ℕ} (hg : 0 < g) :
    1 ≤ (g : ℝ) * padicAbs 2 (g : ℤ) * padicAbs 3 (g : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg_ne : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hg.ne'
  have h2dvd : 2 ^ padicValNat 2 g ∣ g := pow_padicValNat_dvd
  have h3dvd : 3 ^ padicValNat 3 g ∣ g := pow_padicValNat_dvd
  have hcop : Nat.Coprime (2 ^ padicValNat 2 g) (3 ^ padicValNat 3 g) := by
    have : Nat.Coprime 2 3 := by decide
    exact (this.pow_left _).pow_right _
  have h23dvd : 2 ^ padicValNat 2 g * 3 ^ padicValNat 3 g ∣ g :=
    hcop.mul_dvd_of_dvd_of_dvd h2dvd h3dvd
  have h23le : (2 ^ padicValNat 2 g * 3 ^ padicValNat 3 g : ℕ) ≤ g :=
    Nat.le_of_dvd hg h23dvd
  have h23r : (2 : ℝ) ^ padicValNat 2 g * (3 : ℝ) ^ padicValNat 3 g ≤ (g : ℝ) := by
    exact_mod_cast h23le
  unfold padicAbs
  simp only [hg_ne, ↓reduceIte, Int.natAbs_natCast]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ padicValNat 2 g := by positivity
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ padicValNat 3 g := by positivity
  calc
    (1 : ℝ) = ((2 : ℝ) ^ padicValNat 2 g * (3 : ℝ) ^ padicValNat 3 g) *
        ((2 : ℝ) ^ padicValNat 2 g)⁻¹ * ((3 : ℝ) ^ padicValNat 3 g)⁻¹ := by
      field_simp [h2pos.ne', h3pos.ne']
    _ ≤ (g : ℝ) * ((2 : ℝ) ^ padicValNat 2 g)⁻¹ * ((3 : ℝ) ^ padicValNat 3 g)⁻¹ := by
      gcongr

/-- Removing `g = Int.gcd X Z` from `(X, Z)` produces a primitive vector `(x, z)` whose
3-place product is at most that of `(X, Z)` (dividing by `(g |g|_2 |g|_3)^2 ≥ 1`). -/
theorem primitive_threePlaceProduct_le {X Z : ℤ} (hX : X ≠ 0) (hZ : Z ≠ 0) :
    let g : ℕ := Int.gcd X Z
    let x : ℤ := X / (g : ℤ)
    let z : ℤ := Z / (g : ℤ)
    Int.gcd x z = 1 ∧
    x ≠ 0 ∧ z ≠ 0 ∧
    (X ≠ Z → x ≠ z) ∧
    z * X = x * Z ∧
    threePlaceProduct x z ≤ threePlaceProduct X Z := by
  intro g x z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left Z.natAbs (Int.natAbs_pos.mpr hX)
  have hg_ne : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hg_pos.ne'
  have hgX : (g : ℤ) ∣ X := Int.gcd_dvd_left X Z
  have hgZ : (g : ℤ) ∣ Z := Int.gcd_dvd_right X Z
  have hXg : (g : ℤ) * x = X := Int.mul_ediv_cancel' hgX
  have hZg : (g : ℤ) * z = Z := Int.mul_ediv_cancel' hgZ
  have hx_ne : x ≠ 0 := by
    intro hx0; rw [hx0, mul_zero] at hXg; exact hX hXg.symm
  have hz_ne : z ≠ 0 := by
    intro hz0; rw [hz0, mul_zero] at hZg; exact hZ hZg.symm
  have hprim : Int.gcd x z = 1 := by
    have h1 : x.natAbs = X.natAbs / g := by
      have hmul : g * x.natAbs = X.natAbs := by
        have := congrArg Int.natAbs hXg
        simpa [Int.natAbs_mul] using this
      exact Nat.eq_div_of_mul_eq_right hg_pos.ne' hmul
    have h2 : z.natAbs = Z.natAbs / g := by
      have hmul : g * z.natAbs = Z.natAbs := by
        have := congrArg Int.natAbs hZg
        simpa [Int.natAbs_mul] using this
      exact Nat.eq_div_of_mul_eq_right hg_pos.ne' hmul
    change Nat.gcd x.natAbs z.natAbs = 1
    set d := Nat.gcd x.natAbs z.natAbs
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left z.natAbs (Int.natAbs_pos.mpr hx_ne)
    have hgdX : g * d ∣ X.natAbs := by
      have hmulX : g * x.natAbs = X.natAbs := by
        have := congrArg Int.natAbs hXg; simpa [Int.natAbs_mul] using this
      rw [← hmulX]
      exact Nat.mul_dvd_mul_left g (Nat.gcd_dvd_left x.natAbs z.natAbs)
    have hgdZ : g * d ∣ Z.natAbs := by
      have hmulZ : g * z.natAbs = Z.natAbs := by
        have := congrArg Int.natAbs hZg; simpa [Int.natAbs_mul] using this
      rw [← hmulZ]
      exact Nat.mul_dvd_mul_left g (Nat.gcd_dvd_right x.natAbs z.natAbs)
    have hgd_dvd_g : g * d ∣ g := Nat.dvd_gcd hgdX hgdZ
    have hgd_le : g * d ≤ g := Nat.le_of_dvd hg_pos hgd_dvd_g
    have hd_le1 : d ≤ 1 := by nlinarith
    omega
  have hne : X ≠ Z → x ≠ z := by
    intro hXZ hxz; apply hXZ; rw [← hXg, ← hZg, hxz]
  have hline : z * X = x * Z := by
    rw [← hXg, ← hZg]; ring
  have hprod : threePlaceProduct x z ≤ threePlaceProduct X Z := by
    unfold threePlaceProduct
    have hXcast : (X : ℝ) = (g : ℝ) * (x : ℝ) := by exact_mod_cast hXg.symm
    have hZcast : (Z : ℝ) = (g : ℝ) * (z : ℝ) := by exact_mod_cast hZg.symm
    have hXZeq : X * Z = (g : ℤ) * (g : ℤ) * (x * z) := by
      rw [← hXg, ← hZg]; ring
    rw [hXcast, hZcast, hXZeq,
      padicAbs_mul ((g : ℤ) * (g : ℤ)) (x * z), padicAbs_mul (g : ℤ) (g : ℤ),
      padicAbs_mul ((g : ℤ) * (g : ℤ)) (x * z), padicAbs_mul (g : ℤ) (g : ℤ)]
    have hg_r : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr hg_pos
    have hscale :
        |(g : ℝ) * (x : ℝ) - (g : ℝ) * (z : ℝ)| * |(g : ℝ) * (z : ℝ)| *
          (padicAbs 2 (g : ℤ) * padicAbs 2 (g : ℤ) * padicAbs 2 (x * z)) *
          (padicAbs 3 (g : ℤ) * padicAbs 3 (g : ℤ) * padicAbs 3 (x * z)) =
        ((g : ℝ) * padicAbs 2 (g : ℤ) * padicAbs 3 (g : ℤ)) ^ 2 *
          (|(x : ℝ) - (z : ℝ)| * |(z : ℝ)| * padicAbs 2 (x * z) * padicAbs 3 (x * z)) := by
      rw [← mul_sub, abs_mul, abs_mul, abs_of_pos hg_r]
      ring
    rw [hscale]
    have hge1 : 1 ≤ ((g : ℝ) * padicAbs 2 (g : ℤ) * padicAbs 3 (g : ℤ)) ^ 2 := by
      have h1 := nat_mul_padicAbs_two_three_ge_one hg_pos
      nlinarith
    have hnonneg :
        0 ≤ |(x : ℝ) - (z : ℝ)| * |(z : ℝ)| * padicAbs 2 (x * z) * padicAbs 3 (x * z) := by
      have := padicAbs_nonneg 2 (x * z)
      have := padicAbs_nonneg 3 (x * z)
      positivity
    nlinarith
  exact ⟨hprim, hx_ne, hz_ne, hne, hline, hprod⟩

/-- **Algebraic Wrap-Separation Reduction (`wrap-separation.md`, `separation-bands.md`):**
Two distinct shifts `d₁ ≠ d₂` agreeing modulo `2^r` near centers `ν_i * 2^(k+m) / 3^s`
produce a nonzero, non-diagonal integer vector `(X, Z) = (t * 2^(k+m-r), a * 3^s)` with
explicit upper bounds on `|Z - X|`, `|t|`, and the 3-place `{∞, 2, 3}` product. -/
theorem wrap_separation_vector_bounds
    {k m r s : ℕ} {d₁ d₂ ν₁ ν₂ a : ℤ} {R : ℝ}
    (hrle : r ≤ k + m) (hm3 : 3 ≤ m)
    (hdne : d₁ ≠ d₂)
    (hmod : d₂ - d₁ = a * (2 : ℤ) ^ r)
    (hloc1 : |(d₁ : ℝ) - (ν₁ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R)
    (hloc2 : |(d₂ : ℝ) - (ν₂ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R)
    (hnu1 : |(ν₁ : ℝ)| ≤ 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m)
    (hnu2 : |(ν₂ : ℝ)| ≤ 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m)
    (hsepR : 2 * R < (2 : ℝ) ^ r) :
    let t : ℤ := ν₂ - ν₁
    let M : ℤ := (2 : ℤ) ^ (k + m - r)
    let X : ℤ := t * M
    let Z : ℤ := a * (3 : ℤ) ^ s
    a ≠ 0 ∧ t ≠ 0 ∧ X ≠ 0 ∧ Z ≠ 0 ∧ X ≠ Z ∧
    |(Z : ℝ) - (X : ℝ)| ≤ 2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r ∧
    |(t : ℝ)| ≤ 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := by
  intro t M X Z
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at hmod
    exact hdne (sub_eq_zero.mp hmod).symm
  have hdiff_loc :
      |(d₂ : ℝ) - (d₁ : ℝ) - (t : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ 2 * R := by
    have hsplit :
        (d₂ : ℝ) - (d₁ : ℝ) - (t : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s =
          ((d₂ : ℝ) - (ν₂ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s) -
          ((d₁ : ℝ) - (ν₁ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s) := by
      have ht : (t : ℝ) = (ν₂ : ℝ) - (ν₁ : ℝ) := by exact_mod_cast rfl
      rw [ht]; ring
    rw [hsplit]
    calc
      |_ - _| ≤ |(d₂ : ℝ) - (ν₂ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| +
          |(d₁ : ℝ) - (ν₁ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| := abs_sub _ _
      _ ≤ R + R := add_le_add hloc2 hloc1
      _ = 2 * R := by ring
  have ht_ne : t ≠ 0 := by
    intro ht0
    have h1 : |(d₂ : ℝ) - (d₁ : ℝ)| ≤ 2 * R := by
      have ht0r : (t : ℝ) = 0 := by exact_mod_cast ht0
      simpa [ht0r] using hdiff_loc
    have hmodr : (d₂ : ℝ) - (d₁ : ℝ) = (a : ℝ) * (2 : ℝ) ^ r := by exact_mod_cast hmod
    rw [hmodr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)] at h1
    have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
      have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
      exact_mod_cast this
    have hge : (2 : ℝ) ^ r ≤ |(a : ℝ)| * (2 : ℝ) ^ r := by
      calc (2 : ℝ) ^ r = 1 * (2 : ℝ) ^ r := (one_mul _).symm
        _ ≤ |(a : ℝ)| * (2 : ℝ) ^ r := mul_le_mul_of_nonneg_right ha1 (by positivity)
    linarith
  have hM_ne : M ≠ 0 := by positivity
  have h3_ne : (3 : ℤ) ^ s ≠ 0 := by positivity
  have hX_ne : X ≠ 0 := mul_ne_zero ht_ne hM_ne
  have hZ_ne : Z ≠ 0 := mul_ne_zero ha h3_ne
  have ht_bound : |(t : ℝ)| ≤ 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := by
    have htcast : (t : ℝ) = (ν₂ : ℝ) - (ν₁ : ℝ) := by exact_mod_cast rfl
    rw [htcast]
    calc
      |(ν₂ : ℝ) - (ν₁ : ℝ)| ≤ |(ν₂ : ℝ)| + |(ν₁ : ℝ)| := abs_sub _ _
      _ ≤ 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m + 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := add_le_add hnu2 hnu1
      _ = 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := by ring
  have hXZ_ne : X ≠ Z := by
    intro hEq
    -- Since gcd(2^(k+m-r), 3^s) = 1, X = Z forces 3^s ∣ t.natAbs, contradicting 0 < |t| < 3^s.
    have habs : t.natAbs * 2 ^ (k + m - r) = a.natAbs * 3 ^ s := by
      have := congrArg Int.natAbs hEq
      simpa [X, Z, M, Int.natAbs_mul] using this
    have hdvd : 3 ^ s ∣ t.natAbs * 2 ^ (k + m - r) := ⟨a.natAbs, by linarith⟩
    have hcop : Nat.Coprime (3 ^ s) (2 ^ (k + m - r)) := by
      have : Nat.Coprime 3 2 := by decide
      exact (this.pow_left s).pow_right (k + m - r)
    have h3dvd : 3 ^ s ∣ t.natAbs := (hcop.dvd_of_dvd_mul_right hdvd)
    have h3le : 3 ^ s ≤ t.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr ht_ne) h3dvd
    have h3ler : (3 : ℝ) ^ s ≤ |(t : ℝ)| := by
      have : ((t.natAbs : ℕ) : ℝ) = |(t : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [← this]
      exact_mod_cast h3le
    have h2m : (8 : ℝ) ≤ (2 : ℝ) ^ m := by
      have : (2 : ℕ) ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm3
      have : (8 : ℕ) ≤ 2 ^ m := by simpa using this
      exact_mod_cast this
    have hlt : 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m < (3 : ℝ) ^ s := by
      rw [div_lt_iff₀ (by positivity)]
      have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
      nlinarith
    linarith
  have hZX_bound : |(Z : ℝ) - (X : ℝ)| ≤ 2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
    have hscale :
        (Z : ℝ) - (X : ℝ) =
          ((3 : ℝ) ^ s / (2 : ℝ) ^ r) *
            ((d₂ : ℝ) - (d₁ : ℝ) - (t : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s) := by
      have hmodr : (d₂ : ℝ) - (d₁ : ℝ) = (a : ℝ) * (2 : ℝ) ^ r := by exact_mod_cast hmod
      have hpow : (2 : ℝ) ^ (k + m) = (2 : ℝ) ^ (k + m - r) * (2 : ℝ) ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hrle]
      have hXcast : (X : ℝ) = (t : ℝ) * (2 : ℝ) ^ (k + m - r) := by
        change ((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ) = _; push_cast; rfl
      have hZcast : (Z : ℝ) = (a : ℝ) * (3 : ℝ) ^ s := by
        change ((a * (3 : ℤ) ^ s : ℤ) : ℝ) = _; push_cast; rfl
      rw [hmodr, hpow, hXcast, hZcast]
      field_simp [h2pos.ne', h3pos.ne']
    rw [hscale, abs_mul, abs_of_pos (div_pos h3pos h2pos)]
    calc
      (3 : ℝ) ^ s / (2 : ℝ) ^ r *
          |(d₂ : ℝ) - (d₁ : ℝ) - (t : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s|
        ≤ (3 : ℝ) ^ s / (2 : ℝ) ^ r * (2 * R) :=
          mul_le_mul_of_nonneg_left hdiff_loc (by positivity)
      _ = 2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r := by ring
  exact ⟨ha, ht_ne, hX_ne, hZ_ne, hXZ_ne, hZX_bound, ht_bound⟩

/-- **Exact 3-Place `{∞, 2, 3}` Product Bound:**
Because `M = 2^(k+m-r) ∣ X` and `D = 3^s ∣ Z`, the factors `M` and `D` cancel identically,
giving `threePlaceProduct X Z ≤ 24 * R * 3^s / 2^(m + r)`. -/
theorem wrap_separation_three_place_bound
    {k m r s : ℕ} {t a : ℤ} {R : ℝ}
    (ht : t ≠ 0) (ha : a ≠ 0) (hR : 0 ≤ R)
    (hZX : |((a * (3 : ℤ) ^ s : ℤ) : ℝ) - ((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ)| ≤
      2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r)
    (ht_bound : |(t : ℝ)| ≤ 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m)
    (hZle : |((a * (3 : ℤ) ^ s : ℤ) : ℝ)| ≤ 2 * |((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ)|) :
    threePlaceProduct (t * (2 : ℤ) ^ (k + m - r)) (a * (3 : ℤ) ^ s) ≤
      24 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ (m + r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : ℤ := (2 : ℤ) ^ (k + m - r)
  set D : ℤ := (3 : ℤ) ^ s
  set X : ℤ := t * M
  set Z : ℤ := a * D
  have hX : X ≠ 0 := mul_ne_zero ht (by positivity)
  have hZ : Z ≠ 0 := mul_ne_zero ha (by positivity)
  have hXZ : X * Z ≠ 0 := mul_ne_zero hX hZ
  have h2dvd : (2 : ℤ) ^ (k + m - r) ∣ X * Z := dvd_mul_of_dvd_left ⟨t, by ring⟩ Z
  have h3dvd : (3 : ℤ) ^ s ∣ X * Z := dvd_mul_of_dvd_right ⟨a, by ring⟩ X
  have hp2 : padicAbs 2 (X * Z) ≤ ((2 : ℝ) ^ (k + m - r))⁻¹ :=
    padicAbs_le_of_pow_dvd hXZ h2dvd
  have hp3 : padicAbs 3 (X * Z) ≤ ((3 : ℝ) ^ s)⁻¹ :=
    padicAbs_le_of_pow_dvd hXZ h3dvd
  have hXZabs : |(X : ℝ) - (Z : ℝ)| ≤ 2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r := by
    rw [abs_sub_comm]; exact hZX
  have hXabs : |(X : ℝ)| = |(t : ℝ)| * (2 : ℝ) ^ (k + m - r) := by
    have : (X : ℝ) = (t : ℝ) * (2 : ℝ) ^ (k + m - r) := by
      change ((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ) = _; push_cast; rfl
    rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + m - r))]
  have hZabs : |(Z : ℝ)| ≤ 2 * (|(t : ℝ)| * (2 : ℝ) ^ (k + m - r)) := by
    rwa [hXabs] at hZle
  have hMpos : (0 : ℝ) < (2 : ℝ) ^ (k + m - r) := by positivity
  have hDpos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  have h2mpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2rpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  unfold threePlaceProduct
  calc
    |(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)| * padicAbs 2 (X * Z) * padicAbs 3 (X * Z)
      ≤ (2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) *
          (2 * (|(t : ℝ)| * (2 : ℝ) ^ (k + m - r))) *
          ((2 : ℝ) ^ (k + m - r))⁻¹ * ((3 : ℝ) ^ s)⁻¹ := by
        have h1 : |(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)| ≤
            (2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) * (2 * (|(t : ℝ)| * (2 : ℝ) ^ (k + m - r))) :=
          mul_le_mul hXZabs hZabs (abs_nonneg _) (by positivity)
        have h2 : padicAbs 2 (X * Z) * padicAbs 3 (X * Z) ≤
            ((2 : ℝ) ^ (k + m - r))⁻¹ * ((3 : ℝ) ^ s)⁻¹ :=
          mul_le_mul hp2 hp3 (padicAbs_nonneg _ _) (by positivity)
        have hmul := mul_le_mul h1 h2
          (mul_nonneg (padicAbs_nonneg _ _) (padicAbs_nonneg _ _)) (by positivity)
        linarith [show |(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)| * padicAbs 2 (X * Z) * padicAbs 3 (X * Z) =
            (|(X : ℝ) - (Z : ℝ)| * |(Z : ℝ)|) * (padicAbs 2 (X * Z) * padicAbs 3 (X * Z)) by ring,
          show (2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) * (2 * (|(t : ℝ)| * (2 : ℝ) ^ (k + m - r))) *
            ((2 : ℝ) ^ (k + m - r))⁻¹ * ((3 : ℝ) ^ s)⁻¹ =
            ((2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) * (2 * (|(t : ℝ)| * (2 : ℝ) ^ (k + m - r)))) *
            (((2 : ℝ) ^ (k + m - r))⁻¹ * ((3 : ℝ) ^ s)⁻¹) by ring]
    _ = 4 * R * |(t : ℝ)| / (2 : ℝ) ^ r := by
        field_simp [hMpos.ne', hDpos.ne', h2rpos.ne']
        ring
    _ ≤ 4 * R * (6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m) / (2 : ℝ) ^ r := by
        gcongr
    _ = 24 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ (m + r) := by
        rw [pow_add]; field_simp [h2mpos.ne', h2rpos.ne']; ring

/-- **Slope-Band Ratio Theorem (`separation-bands.md`):**
If two shells `k₁, k₂` produce nonzero non-diagonal integer vectors `(X₁, Z₁), (X₂, Z₂)` on
the SAME rational line `Z/X = p/q ≠ 1`, with `|X₁| ≤ 2^(c_hi * k₁)` and
`|Z₂ / X₂ - 1| ≤ 2^(-c_lo * k₂)`, then `c_lo * k₂ ≤ c_hi * k₁`. -/
theorem slope_band_ratio {X₁ Z₁ X₂ Z₂ : ℤ} {c_lo c_hi : ℝ} {k₁ k₂ : ℕ}
    (hX₁ : X₁ ≠ 0) (hX₂ : X₂ ≠ 0) (hnd : X₁ ≠ Z₁)
    (hline : Z₁ * X₂ = Z₂ * X₁)
    (hhi : |(X₁ : ℝ)| ≤ (2 : ℝ) ^ (c_hi * (k₁ : ℝ)))
    (hlo : |(Z₂ : ℝ) / (X₂ : ℝ) - 1| ≤ (2 : ℝ) ^ (-c_lo * (k₂ : ℝ))) :
    c_lo * (k₂ : ℝ) ≤ c_hi * (k₁ : ℝ) := by
  set g : ℕ := Int.gcd X₁ Z₁
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left Z₁.natAbs (Int.natAbs_pos.mpr hX₁)
  set x₁ : ℤ := X₁ / (g : ℤ)
  set z₁ : ℤ := Z₁ / (g : ℤ)
  have hXg : (g : ℤ) * x₁ = X₁ := Int.mul_ediv_cancel' (Int.gcd_dvd_left X₁ Z₁)
  have hZg : (g : ℤ) * z₁ = Z₁ := Int.mul_ediv_cancel' (Int.gcd_dvd_right X₁ Z₁)
  have hx₁_ne : x₁ ≠ 0 := by intro h0; rw [h0, mul_zero] at hXg; exact hX₁ hXg.symm
  have hne : z₁ - x₁ ≠ 0 := by
    intro h0
    apply hnd
    have : z₁ = x₁ := sub_eq_zero.mp h0
    rw [← hXg, ← hZg, this]
  have hratio : (Z₂ : ℝ) / (X₂ : ℝ) = (z₁ : ℝ) / (x₁ : ℝ) := by
    have hX₂r : (X₂ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hX₂
    have hx₁r : (x₁ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hx₁_ne
    have hgr : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    have hlr : (Z₁ : ℝ) * (X₂ : ℝ) = (Z₂ : ℝ) * (X₁ : ℝ) := by exact_mod_cast hline
    have hX1r : (X₁ : ℝ) = (g : ℝ) * (x₁ : ℝ) := by exact_mod_cast hXg.symm
    have hZ1r : (Z₁ : ℝ) = (g : ℝ) * (z₁ : ℝ) := by exact_mod_cast hZg.symm
    rw [hX1r, hZ1r] at hlr
    have hmul : (z₁ : ℝ) * (X₂ : ℝ) = (Z₂ : ℝ) * (x₁ : ℝ) := by
      have : (g : ℝ) * ((z₁ : ℝ) * (X₂ : ℝ)) = (g : ℝ) * ((Z₂ : ℝ) * (x₁ : ℝ)) := by linarith
      exact mul_left_cancel₀ hgr this
    field_simp [hX₂r, hx₁r]
    linarith
  have h1 : (1 : ℝ) / |(x₁ : ℝ)| ≤ |(Z₂ : ℝ) / (X₂ : ℝ) - 1| := by
    rw [hratio]
    have hx₁r : (x₁ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hx₁_ne
    have hsub : (z₁ : ℝ) / (x₁ : ℝ) - 1 = ((z₁ - x₁ : ℤ) : ℝ) / (x₁ : ℝ) := by
      push_cast; field_simp [hx₁r]
    rw [hsub, abs_div]
    have hge1 : (1 : ℝ) ≤ |((z₁ - x₁ : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |z₁ - x₁| := Int.one_le_abs hne
      exact_mod_cast this
    exact div_le_div_of_nonneg_right hge1 (abs_nonneg _)
  have hq_le : |(x₁ : ℝ)| ≤ |(X₁ : ℝ)| := by
    have hX1r : (X₁ : ℝ) = (g : ℝ) * (x₁ : ℝ) := by exact_mod_cast hXg.symm
    rw [hX1r, abs_mul, abs_of_pos (by exact_mod_cast hg_pos : (0 : ℝ) < (g : ℝ))]
    have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_pos
    nlinarith [abs_nonneg (x₁ : ℝ)]
  have hx₁_pos : 0 < |(x₁ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hx₁_ne)
  have hpow_le : (2 : ℝ) ^ (c_lo * (k₂ : ℝ)) ≤ (2 : ℝ) ^ (c_hi * (k₁ : ℝ)) := by
    have hinv : (2 : ℝ) ^ (c_lo * (k₂ : ℝ)) ≤ |(x₁ : ℝ)| := by
      have h2 := h1.trans hlo
      rw [neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div] at h2
      have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (c_lo * (k₂ : ℝ))
      exact (inv_le_inv₀ hx₁_pos hpos).mp h2
    exact hinv.trans (hq_le.trans hhi)
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow_le

/-! ## 4. Explicit Quantitative Subspace Theorem Interface & Band Covering -/

/-- Explicit interface to Schlickewei (1990) / Evertse–Ferretti (2013) Theorem 3.1 for the
3-place system `S = {∞, 2, 3}` with forms `(X - Z, Z)` at `∞` and `(X, Z)` at `2, 3`.
Declared as an explicit structure parameter (NEVER an axiom). -/
structure ThreePlaceSubspaceHypothesis (δ H₀ : ℝ) (R : ℕ) where
  slopes : Fin R → ℚ
  covers :
    ∀ x z : ℤ, Int.gcd x z = 1 → x ≠ 0 → z ≠ 0 → x ≠ z →
      H₀ ≤ max |(x : ℝ)| |(z : ℝ)| →
      threePlaceProduct x z < ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) ^ (-δ / 2) →
      ∃ i : Fin R, (z : ℚ) / (x : ℚ) = slopes i

/-- Given `ThreePlaceSubspaceHypothesis`, any set of exceptional shells `E` above `k_*`
whose violating vectors satisfy the slope/norm/height bounds is covered by at most `R`
closed bands `[K_i, (c_hi / c_lo) * K_i]` with integer left endpoints `K_i ≥ k_*`. -/
theorem subspace_implies_exceptional_bands
    {δ H₀ c_lo c_hi : ℝ} {R k_star : ℕ}
    (hc_lo : 0 < c_lo)
    (hsub : ThreePlaceSubspaceHypothesis δ H₀ R)
    (E : ℕ → Prop)
    (hwit : ∀ k : ℕ, k_star ≤ k → E k →
      ∃ X Z : ℤ, X ≠ 0 ∧ Z ≠ 0 ∧ X ≠ Z ∧
        H₀ ≤ max |(X / (Int.gcd X Z : ℤ) : ℝ)| |(Z / (Int.gcd X Z : ℤ) : ℝ)| ∧
        threePlaceProduct X Z <
          (((X / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2 + ((Z / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2) ^ (-δ / 2) ∧
        |(X : ℝ)| ≤ (2 : ℝ) ^ (c_hi * (k : ℝ)) ∧
        |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-c_lo * (k : ℝ))) :
    ∃ K_left : Fin R → ℕ,
      (∀ i, k_star ≤ K_left i) ∧
      ∀ k : ℕ, k_star ≤ k → E k →
        ∃ i : Fin R, K_left i ≤ k ∧ (k : ℝ) ≤ (c_hi / c_lo) * (K_left i : ℝ) := by
  classical
  -- Helper predicate: shell k hits line i via a valid witness.
  let Hits (i : Fin R) (k : ℕ) : Prop :=
    k_star ≤ k ∧ E k ∧
      ∃ X Z : ℤ, X ≠ 0 ∧ Z ≠ 0 ∧ X ≠ Z ∧
        (Z : ℚ) / (X : ℚ) = hsub.slopes i ∧
        |(X : ℝ)| ≤ (2 : ℝ) ^ (c_hi * (k : ℝ)) ∧
        |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-c_lo * (k : ℝ))
  let K_left : Fin R → ℕ := fun i =>
    if h : ∃ k, Hits i k then Nat.find h else k_star
  refine ⟨K_left, ?_, ?_⟩
  · intro i
    dsimp [K_left]
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_rfl
  · intro k hk hEk
    obtain ⟨X, Z, hX, hZ, hXZ, hH, hprod, hhi, hlo⟩ := hwit k hk hEk
    obtain ⟨hprim, hx_ne, hz_ne, hxz_ne, hline_prim, hprod_le⟩ :=
      primitive_threePlaceProduct_le hX hZ
    set g : ℕ := Int.gcd X Z
    set x : ℤ := X / (g : ℤ)
    set z : ℤ := Z / (g : ℤ)
    have hH' : H₀ ≤ max |(x : ℝ)| |(z : ℝ)| := by
      have hx_cast : (x : ℝ) = (X / (g : ℤ) : ℝ) := by
        have hgX : (g : ℤ) ∣ X := Int.gcd_dvd_left X Z
        have hXg : (g : ℤ) * x = X := Int.mul_ediv_cancel' hgX
        have hg_ne : (g : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left Z.natAbs (Int.natAbs_pos.mpr hX)).ne'
        have hXcast : (X : ℝ) = (g : ℝ) * (x : ℝ) := by exact_mod_cast hXg.symm
        rw [hXcast, Int.cast_natCast, mul_div_cancel_left₀ _ hg_ne]
      have hz_cast : (z : ℝ) = (Z / (g : ℤ) : ℝ) := by
        have hgZ : (g : ℤ) ∣ Z := Int.gcd_dvd_right X Z
        have hZg : (g : ℤ) * z = Z := Int.mul_ediv_cancel' hgZ
        have hg_ne : (g : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left Z.natAbs (Int.natAbs_pos.mpr hX)).ne'
        have hZcast : (Z : ℝ) = (g : ℝ) * (z : ℝ) := by exact_mod_cast hZg.symm
        rw [hZcast, Int.cast_natCast, mul_div_cancel_left₀ _ hg_ne]
      simpa [hx_cast, hz_cast] using hH
    have hprod' : threePlaceProduct x z < ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) ^ (-δ / 2) :=
      lt_of_le_of_lt hprod_le hprod
    obtain ⟨i, hi⟩ := hsub.covers x z hprim hx_ne hz_ne (hxz_ne hXZ) hH' hprod'
    have hslope : (Z : ℚ) / (X : ℚ) = hsub.slopes i := by
      have hXq : (X : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hX
      have hxq : (x : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hx_ne
      have hmulq : (z : ℚ) * (X : ℚ) = (x : ℚ) * (Z : ℚ) := by exact_mod_cast hline_prim
      rw [← hi]
      field_simp [hXq, hxq]
      linarith
    have hHitk : Hits i k := ⟨hk, hEk, X, Z, hX, hZ, hXZ, hslope, hhi, hlo⟩
    have hex : ∃ m, Hits i m := ⟨k, hHitk⟩
    have hKi_eq : K_left i = Nat.find hex := by simp [K_left, hex]
    have hKi_le : K_left i ≤ k := by rw [hKi_eq]; exact Nat.find_min' hex hHitk
    obtain ⟨_, _, X₁, Z₁, hX₁, hZ₁, hXZ₁, hslope₁, hhi₁, _⟩ := Nat.find_spec hex
    have hline : Z₁ * X = Z * X₁ := by
      have h1 : (Z₁ : ℚ) / (X₁ : ℚ) = (Z : ℚ) / (X : ℚ) := hslope₁.trans hslope.symm
      have hX1q : (X₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hX₁
      have hXq : (X : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hX
      have hmulq : (Z₁ : ℚ) * (X : ℚ) = (Z : ℚ) * (X₁ : ℚ) := by
        field_simp [hX1q, hXq] at h1; linarith
      exact_mod_cast hmulq
    have hratio := slope_band_ratio hX₁ hX hXZ₁ hline hhi₁ hlo
    refine ⟨i, hKi_le, ?_⟩
    rw [hKi_eq]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc_lo]
    linarith

/-! ## 5. Cumulative `N_T(X) ≤ 5 X^a`, Good-Scale Window, and Eventual `O(X^a)` -/

/-- Explicit shell-count covering hypothesis matching `exceptional-scale-count.md`. -/
structure ShellSeparationCovering where
  a : ℝ
  b : ℝ
  ρ_band : ℝ
  K : ℕ
  R : ℕ
  leftEnds : Fin R → ℕ
  ha_gt : (7 : ℝ) / 8 < a
  hab : a < b
  hb_lt : b < 1
  hρ_nonneg : 0 ≤ ρ_band
  hK : 2 ≤ K
  hleft_ge : ∀ i : Fin R, K ≤ leftEnds i
  hall : ∀ k : ℕ, K ≤ k → (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ (b * (k : ℝ))
  hgood : ∀ k : ℕ, K ≤ k →
    (∀ i : Fin R, ¬ (leftEnds i ≤ k ∧ (k : ℝ) ≤ ρ_band * (leftEnds i : ℝ))) →
    (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ (a * (k : ℝ))

/-- Decomposition of `N_T X` into starts `< 2^K` plus dyadic shells `k ∈ [K, Nat.log 2 X]`. -/
theorem N_T_le_two_pow_add_sum_shells (K X : ℕ) :
    N_T X ≤ 2 ^ K + ∑ k ∈ Finset.Icc K (Nat.log 2 X), shellNeverDrops k := by
  classical
  unfold N_T shellNeverDrops
  set A := (Finset.Icc 1 X).filter (fun n => NeverDrops n)
  set A_small := A.filter (fun n => n < 2 ^ K)
  set A_large := A.filter (fun n => ¬ (n < 2 ^ K))
  have hcard_split : A.card = A_small.card + A_large.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext n; simp only [A_small, A_large, Finset.mem_union, Finset.mem_filter]; tauto
    · rw [Finset.disjoint_left]; intro n h1 h2; simp [A_small, A_large] at h1 h2; omega
  have hsmall : A_small.card ≤ 2 ^ K := by
    calc
      A_small.card ≤ (Finset.range (2 ^ K)).card := by
        apply Finset.card_le_card
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      _ = 2 ^ K := Finset.card_range _
  have hlarge : A_large.card ≤ ∑ k ∈ Finset.Icc K (Nat.log 2 X),
      ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => NeverDrops n)).card := by
    calc
      A_large.card ≤ ((Finset.Icc K (Nat.log 2 X)).biUnion
          (fun k => (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => NeverDrops n))).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [A_large, A, Finset.mem_filter, Finset.mem_Icc, not_lt] at hn
        obtain ⟨⟨⟨hn1, hnX⟩, hnd⟩, hnK⟩ := hn
        refine Finset.mem_biUnion.mpr ⟨Nat.log 2 n, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨Nat.le_log_of_pow_le (by decide) hnK, Nat.log_mono_right hnX⟩
        · rw [Finset.mem_filter, Finset.mem_Ico]
          exact ⟨⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by decide) n⟩, hnd⟩
      _ ≤ _ := Finset.card_biUnion_le
  omega

/-- Geometric series upper bound: for `c > 0` and `M : ℕ`,
`∑ k ∈ range (M + 1), 2^(c * k) ≤ 2^(c * M) / (1 - 2^(-c))`. -/
theorem sum_two_rpow_le {c : ℝ} (hc : 0 < c) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), (2 : ℝ) ^ (c * (k : ℝ)) ≤
      (2 : ℝ) ^ (c * (M : ℝ)) / (1 - (2 : ℝ) ^ (-c)) := by
  have hr_lt : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hc)
  have hr_pos : 0 < (2 : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by norm_num) (-c)
  have hden : 0 < 1 - (2 : ℝ) ^ (-c) := sub_pos.mpr hr_lt
  -- Rewrite k-th term as 2^(c*M) * (2^(-c))^(M - k).
  have hrew :
      ∑ k ∈ Finset.range (M + 1), (2 : ℝ) ^ (c * (k : ℝ)) =
        (2 : ℝ) ^ (c * (M : ℝ)) * ∑ j ∈ Finset.range (M + 1), ((2 : ℝ) ^ (-c)) ^ j := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_range_reflect (fun j => (2 : ℝ) ^ (c * (M : ℝ)) * ((2 : ℝ) ^ (-c)) ^ j) (M + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : M + 1 - 1 - k = M - k := by omega
    rw [hsub, ← Real.rpow_natCast ((2 : ℝ) ^ (-c)) (M - k),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    have hcast : ((M - k : ℕ) : ℝ) = (M : ℝ) - (k : ℝ) := Nat.cast_sub hkM
    rw [hcast]; ring
  rw [hrew, geom_sum_eq hr_lt.ne]
  have hgeom : (1 - ((2 : ℝ) ^ (-c)) ^ (M + 1)) / (1 - (2 : ℝ) ^ (-c)) ≤ 1 / (1 - (2 : ℝ) ^ (-c)) := by
    have : 0 ≤ ((2 : ℝ) ^ (-c)) ^ (M + 1) := pow_nonneg hr_pos.le _
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hneg : (((2 : ℝ) ^ (-c)) ^ (M + 1) - 1) / ((2 : ℝ) ^ (-c) - 1) =
      (1 - ((2 : ℝ) ^ (-c)) ^ (M + 1)) / (1 - (2 : ℝ) ^ (-c)) := by
    field_simp [hden.ne', (sub_ne_zero.mpr hr_lt.ne)]
    ring
  rw [hneg]
  calc
    (2 : ℝ) ^ (c * (M : ℝ)) * ((1 - ((2 : ℝ) ^ (-c)) ^ (M + 1)) / (1 - (2 : ℝ) ^ (-c)))
      ≤ (2 : ℝ) ^ (c * (M : ℝ)) * (1 / (1 - (2 : ℝ) ^ (-c))) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (2 : ℝ) ^ (c * (M : ℝ)) / (1 - (2 : ℝ) ^ (-c)) := by ring

/-- For any `c > 7/8`, `(1 - 2^(-c))⁻¹ < 9 / 4` (from `(9/5)^8 < 2^7`). -/
theorem inv_one_sub_two_neg_lt_nine_fourths {c : ℝ} (hc : (7 : ℝ) / 8 < c) :
    (1 - (2 : ℝ) ^ (-c))⁻¹ < (9 : ℝ) / 4 := by
  have h1 : (2 : ℝ) ^ (-c) < (2 : ℝ) ^ (-(7 : ℝ) / 8) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)
  have h2 : (2 : ℝ) ^ (-(7 : ℝ) / 8) < (5 : ℝ) / 9 := by
    have hpow : ((2 : ℝ) ^ (-(7 : ℝ) / 8)) ^ (8 : ℕ) < ((5 : ℝ) / 9) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(7 : ℝ) / 8)) 8,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hexp : -(7 : ℝ) / 8 * (8 : ℕ) = (-7 : ℤ) := by norm_num
      rw [hexp, Real.rpow_intCast]
      norm_num
    by_contra hge
    push Not at hge
    have : ((5 : ℝ) / 9) ^ (8 : ℕ) ≤ ((2 : ℝ) ^ (-(7 : ℝ) / 8)) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hge 8
    linarith
  have hlt59 : (2 : ℝ) ^ (-c) < (5 : ℝ) / 9 := h1.trans h2
  have hden : (4 : ℝ) / 9 < 1 - (2 : ℝ) ^ (-c) := by linarith
  have hinv := (inv_lt_inv₀ (by linarith) (by norm_num : (0 : ℝ) < 4 / 9)).mpr hden
  linarith [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]

/-- **Cumulative Count Outside Exceptional Scale Ranges (`exceptional-scale-count.md`):**
Under `cov : ShellSeparationCovering` with `ρ_band * b ≤ 3.06 * a`, every `X ≥ 2^(2K)`
outside all `R` closed scale ranges `[2^{K_i}, (2^{K_i})^{3.06}]` satisfies `N_T(X) ≤ 5 X^a`. -/
theorem cumulative_count_outside_bands (cov : ShellSeparationCovering)
    (hband : cov.ρ_band * cov.b ≤ ((306 : ℝ) / 100) * cov.a)
    (X : ℕ) (hX : 2 ^ (2 * cov.K) ≤ X)
    (hXout : ∀ i : Fin cov.R,
      ¬ ((2 : ℝ) ^ (cov.leftEnds i) ≤ (X : ℝ) ∧
          (X : ℝ) ≤ ((2 : ℝ) ^ (cov.leftEnds i)) ^ ((306 : ℝ) / 100))) :
    (N_T X : ℝ) ≤ 5 * (X : ℝ) ^ cov.a := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hXr_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hXpos
  have ha_pos : 0 < cov.a := by linarith [cov.ha_gt]
  have hb_pos : 0 < cov.b := by linarith [cov.ha_gt, cov.hab]
  set L : ℝ := Real.logb 2 (X : ℝ)
  have h2L : (2 : ℝ) ^ L = (X : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hXr_pos
  have hX_ge_K : (2 : ℝ) ^ (2 * cov.K) ≤ (X : ℝ) := by exact_mod_cast hX
  have h2K_le : (2 : ℝ) ^ cov.K ≤ (X : ℝ) ^ cov.a / 2 := by
    have h1 : (2 : ℝ) ^ (cov.K + 1) ≤ (2 : ℝ) ^ (cov.a * (2 * cov.K : ℕ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (cov.K + 1)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hKr : (2 : ℝ) ≤ (cov.K : ℝ) := by exact_mod_cast cov.hK
      push_cast
      nlinarith [cov.ha_gt]
    have h2 : (2 : ℝ) ^ (cov.a * (2 * cov.K : ℕ)) ≤ (X : ℝ) ^ cov.a := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      exact Real.rpow_le_rpow (by positivity) hX_ge_K ha_pos.le
    have h3 : (2 : ℝ) ^ (cov.K + 1) = 2 * (2 : ℝ) ^ cov.K := by ring
    linarith
  -- Split Icc K (Nat.log 2 X) into good shells and exceptional shells.
  set S_all := Finset.Icc cov.K (Nat.log 2 X)
  let IsBad (k : ℕ) : Prop :=
    ∃ i : Fin cov.R, cov.leftEnds i ≤ k ∧ (k : ℝ) ≤ cov.ρ_band * (cov.leftEnds i : ℝ)
  set S_good := S_all.filter (fun k => ¬ IsBad k)
  set S_bad := S_all.filter (fun k => IsBad k)
  have hN1 : (N_T X : ℝ) ≤ (2 : ℝ) ^ cov.K +
      ∑ k ∈ S_all, (shellNeverDrops k : ℝ) := by
    exact_mod_cast N_T_le_two_pow_add_sum_shells cov.K X
  have hsplit : ∑ k ∈ S_all, (shellNeverDrops k : ℝ) =
      (∑ k ∈ S_good, (shellNeverDrops k : ℝ)) + (∑ k ∈ S_bad, (shellNeverDrops k : ℝ)) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not S_all IsBad (fun k => (shellNeverDrops k : ℝ))).symm
  -- Bound the good shells: every k ∈ S_good has k ≤ Nat.log 2 X and 2^k ≤ X.
  have hlog_le : (Nat.log 2 X : ℝ) ≤ L := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 X : ℕ) ≤ (X : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hXpos.ne'
    rw [← h2L, ← Real.rpow_natCast (2 : ℝ)] at hpow
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  have hgood_sum :
      ∑ k ∈ S_good, (shellNeverDrops k : ℝ) ≤ (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.a)) := by
    calc
      ∑ k ∈ S_good, (shellNeverDrops k : ℝ)
        ≤ ∑ k ∈ S_good, (2 : ℝ) ^ (cov.a * (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_filter] at hk
          have hkK : cov.K ≤ k := (Finset.mem_Icc.mp hk.1).1
          have hnotbad : ∀ i : Fin cov.R, ¬ (cov.leftEnds i ≤ k ∧
              (k : ℝ) ≤ cov.ρ_band * (cov.leftEnds i : ℝ)) := not_exists.mp hk.2
          exact cov.hgood k hkK hnotbad
      _ ≤ ∑ k ∈ Finset.range (Nat.log 2 X + 1), (2 : ℝ) ^ (cov.a * (k : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
          · intro _ _ _; positivity
      _ ≤ (2 : ℝ) ^ (cov.a * (Nat.log 2 X : ℝ)) / (1 - (2 : ℝ) ^ (-cov.a)) :=
          sum_two_rpow_le ha_pos (Nat.log 2 X)
      _ ≤ (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.a)) := by
          have hden : 0 < 1 - (2 : ℝ) ^ (-cov.a) :=
            sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha_pos))
          apply div_le_div_of_nonneg_right _ hden.le
          rw [← h2L, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm L cov.a]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hlog_le ha_pos.le)
  -- Bound the bad shells: every k ∈ S_bad satisfies b * k ≤ a * L!
  have hbad_bound : ∀ k ∈ S_bad, cov.b * (k : ℝ) ≤ cov.a * L := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hk_le_L : (k : ℝ) ≤ L := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk.1).2) hlog_le
    rcases hk.2 with ⟨i, hle_k, hk_le_band⟩
    have hY_le_X : (2 : ℝ) ^ (cov.leftEnds i) ≤ (X : ℝ) := by
      rw [← h2L, ← Real.rpow_natCast (2 : ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact le_trans (by exact_mod_cast hle_k) hk_le_L
    have hX_gt_top : ((2 : ℝ) ^ (cov.leftEnds i)) ^ ((306 : ℝ) / 100) < (X : ℝ) := by
      have hnot := hXout i
      push Not at hnot
      exact hnot hY_le_X
    have hL_gt : ((306 : ℝ) / 100) * (cov.leftEnds i : ℝ) < L := by
      rw [← h2L, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hX_gt_top
      have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hX_gt_top
      linarith
    calc
      cov.b * (k : ℝ) ≤ cov.b * (cov.ρ_band * (cov.leftEnds i : ℝ)) :=
        mul_le_mul_of_nonneg_left hk_le_band hb_pos.le
      _ = (cov.ρ_band * cov.b) * (cov.leftEnds i : ℝ) := by ring
      _ ≤ (((306 : ℝ) / 100) * cov.a) * (cov.leftEnds i : ℝ) :=
        mul_le_mul_of_nonneg_right hband (Nat.cast_nonneg _)
      _ = cov.a * (((306 : ℝ) / 100) * (cov.leftEnds i : ℝ)) := by ring
      _ ≤ cov.a * L := mul_le_mul_of_nonneg_left hL_gt.le ha_pos.le
  set M_bad : ℕ := Nat.floor (cov.a * L / cov.b)
  have hL_nonneg : 0 ≤ L := by
    have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
    rw [← h2L] at this
    by_contra hneg
    push Not at hneg
    have : (2 : ℝ) ^ L < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
    linarith
  have hbad_sum :
      ∑ k ∈ S_bad, (shellNeverDrops k : ℝ) ≤ (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.b)) := by
    calc
      ∑ k ∈ S_bad, (shellNeverDrops k : ℝ)
        ≤ ∑ k ∈ S_bad, (2 : ℝ) ^ (cov.b * (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact cov.hall k (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      _ ≤ ∑ k ∈ Finset.range (M_bad + 1), (2 : ℝ) ^ (cov.b * (k : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_range]
            have hbk : (k : ℝ) ≤ cov.a * L / cov.b := (le_div_iff₀ hb_pos).mpr (by
              have := hbad_bound k hk; linarith)
            exact Nat.lt_succ_of_le (Nat.le_floor hbk)
          · intro _ _ _; positivity
      _ ≤ (2 : ℝ) ^ (cov.b * (M_bad : ℝ)) / (1 - (2 : ℝ) ^ (-cov.b)) :=
          sum_two_rpow_le hb_pos M_bad
      _ ≤ (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.b)) := by
          have hden : 0 < 1 - (2 : ℝ) ^ (-cov.b) :=
            sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hb_pos))
          apply div_le_div_of_nonneg_right _ hden.le
          rw [← h2L, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm L cov.a]
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hfl : (M_bad : ℝ) ≤ cov.a * L / cov.b :=
            Nat.floor_le (div_nonneg (mul_nonneg ha_pos.le hL_nonneg) hb_pos.le)
          have := mul_le_mul_of_nonneg_left hfl hb_pos.le
          rwa [mul_div_cancel₀ _ hb_pos.ne'] at this
  have hga : (1 - (2 : ℝ) ^ (-cov.a))⁻¹ < 9 / 4 :=
    inv_one_sub_two_neg_lt_nine_fourths cov.ha_gt
  have hgb : (1 - (2 : ℝ) ^ (-cov.b))⁻¹ < 9 / 4 :=
    inv_one_sub_two_neg_lt_nine_fourths (cov.ha_gt.trans cov.hab)
  have hXap : 0 ≤ (X : ℝ) ^ cov.a := by positivity
  calc
    (N_T X : ℝ) ≤ (2 : ℝ) ^ cov.K +
        ((X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.a)) +
         (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.b))) := by
      linarith [hN1, hsplit, hgood_sum, hbad_sum]
    _ = (2 : ℝ) ^ cov.K +
        (X : ℝ) ^ cov.a * ((1 - (2 : ℝ) ^ (-cov.a))⁻¹ + (1 - (2 : ℝ) ^ (-cov.b))⁻¹) := by
      ring
    _ ≤ (X : ℝ) ^ cov.a / 2 + (X : ℝ) ^ cov.a * (9 / 4 + 9 / 4) := by
      have : (X : ℝ) ^ cov.a * ((1 - (2 : ℝ) ^ (-cov.a))⁻¹ + (1 - (2 : ℝ) ^ (-cov.b))⁻¹) ≤
          (X : ℝ) ^ cov.a * (9 / 4 + 9 / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hXap
      linarith [h2K_le]
    _ = 5 * (X : ℝ) ^ cov.a := by ring

/-- Helper iteration for `good_scale_in_window`: `x_0 = ⌈X_1⌉`, `x_{j+1} = ⌈x_j^{3.1}⌉`. -/
noncomputable def scaleSeq (X₁ : ℝ) : ℕ → ℕ
  | 0 => Nat.ceil X₁
  | j + 1 => Nat.ceil (((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10))

/-- **Good-Scale Window Pigeonhole Theorem (`exceptional-scale-count.md`):**
For any `R` exceptional intervals `[Y_i, Y_i^{3.06}]` (`Y_i ≥ 1`) and any `X_1 ≥ 2^{10}`,
the interval `[X_1, X_1^{3.2^{R+1}}]` contains an integer `x` outside all `R` intervals. -/
theorem good_scale_in_window (R : ℕ) (Y : Fin R → ℝ) (hY : ∀ i, 1 ≤ Y i)
    (X₁ : ℝ) (hX₁ : (2 : ℝ) ^ 10 ≤ X₁) :
    ∃ x : ℕ,
      X₁ ≤ (x : ℝ) ∧
      (x : ℝ) ≤ X₁ ^ (((32 : ℝ) / 10) ^ (R + 1)) ∧
      ∀ i : Fin R, ¬ (Y i ≤ (x : ℝ) ∧ (x : ℝ) ≤ (Y i) ^ ((306 : ℝ) / 100)) := by
  classical
  have hX₁_ge2 : (2 : ℝ) ≤ X₁ := by linarith [show (2 : ℝ) ≤ (2 : ℝ) ^ 10 by norm_num]
  have hX₁_pos : 0 < X₁ := by linarith
  -- Lower bound: scaleSeq X₁ j ≥ 2^10 and strictly increasing with x_{j+1} ≥ x_j^(3.1) > x_j^(3.06).
  have hge : ∀ j : ℕ, (2 : ℝ) ^ 10 ≤ (scaleSeq X₁ j : ℝ) := by
    intro j
    induction j with
    | zero => exact hX₁.trans (Nat.le_ceil X₁)
    | succ j ih =>
        have h1 : (scaleSeq X₁ j : ℝ) ≤ ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) := by
          have hge1 : (1 : ℝ) ≤ (scaleSeq X₁ j : ℝ) := by linarith [show (1 : ℝ) ≤ (2 : ℝ) ^ 10 by norm_num]
          calc (scaleSeq X₁ j : ℝ) = ((scaleSeq X₁ j : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) :=
              Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
        exact ih.trans (h1.trans (Nat.le_ceil _))
  have hmono : StrictMono (scaleSeq X₁) := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hj : (2 : ℝ) ^ 10 ≤ (scaleSeq X₁ j : ℝ) := hge j
    have hj_gt1 : (1 : ℝ) < (scaleSeq X₁ j : ℝ) := by linarith [show (1 : ℝ) < (2 : ℝ) ^ 10 by norm_num]
    have hlt : (scaleSeq X₁ j : ℝ) < ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) := by
      calc (scaleSeq X₁ j : ℝ) = ((scaleSeq X₁ j : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ < ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) :=
          Real.rpow_lt_rpow_of_exponent_lt hj_gt1 (by norm_num)
    exact_mod_cast hlt.trans_le (Nat.le_ceil _)
  -- Upper bound: scaleSeq X₁ j ≤ X₁^(3.2^(j+1)).
  have hupper : ∀ j : ℕ, (scaleSeq X₁ j : ℝ) ≤ X₁ ^ (((32 : ℝ) / 10) ^ (j + 1)) := by
    intro j
    induction j with
    | zero =>
        have hceil : (Nat.ceil X₁ : ℝ) ≤ 2 * X₁ := by
          have hlt := Nat.ceil_lt_add_one hX₁_pos.le
          linarith
        have h2X : 2 * X₁ ≤ X₁ ^ ((32 : ℝ) / 10) := by
          have h2le : (2 : ℝ) ≤ X₁ ^ ((22 : ℝ) / 10) := by
            have h1 : (2 : ℝ) ≤ ((2 : ℝ) ^ 10) ^ ((22 : ℝ) / 10) := by
              rw [← Real.rpow_natCast (2 : ℝ) 10, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
              calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (2 : ℝ) ^ ((10 : ℕ) * ((22 : ℝ) / 10)) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            exact h1.trans (Real.rpow_le_rpow (by positivity) hX₁ (by norm_num))
          calc 2 * X₁ ≤ X₁ ^ ((22 : ℝ) / 10) * X₁ ^ (1 : ℝ) := by
                rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_right h2le hX₁_pos.le
            _ = X₁ ^ ((32 : ℝ) / 10) := by
                rw [← Real.rpow_add hX₁_pos]; norm_num
        simpa [scaleSeq] using hceil.trans h2X
    | succ j ih =>
        have hj : (2 : ℝ) ^ 10 ≤ (scaleSeq X₁ j : ℝ) := hge j
        have hj_pos : (0 : ℝ) < (scaleSeq X₁ j : ℝ) := by linarith [show (0 : ℝ) < (2 : ℝ) ^ 10 by norm_num]
        have hpow_ge1 : (1 : ℝ) ≤ ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) :=
          Real.one_le_rpow (by linarith [show (1 : ℝ) ≤ (2 : ℝ) ^ 10 by norm_num]) (by norm_num)
        have hceil : (scaleSeq X₁ (j + 1) : ℝ) ≤ 2 * ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) := by
          have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10))
          change (Nat.ceil _ : ℝ) ≤ _
          linarith
        have h2le : (2 : ℝ) ≤ ((scaleSeq X₁ j : ℝ)) ^ ((1 : ℝ) / 10) := by
          have h1 : (2 : ℝ) = ((2 : ℝ) ^ 10) ^ ((1 : ℝ) / 10) := by
            rw [← Real.rpow_natCast (2 : ℝ) 10, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          rw [h1]
          exact Real.rpow_le_rpow (by positivity) hj (by norm_num)
        have hstep : 2 * ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) ≤
            ((scaleSeq X₁ j : ℝ)) ^ ((32 : ℝ) / 10) := by
          calc
            2 * ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10)
              ≤ ((scaleSeq X₁ j : ℝ)) ^ ((1 : ℝ) / 10) * ((scaleSeq X₁ j : ℝ)) ^ ((31 : ℝ) / 10) :=
                mul_le_mul_of_nonneg_right h2le (by positivity)
            _ = ((scaleSeq X₁ j : ℝ)) ^ ((32 : ℝ) / 10) := by
                rw [← Real.rpow_add hj_pos]; norm_num
        calc
          (scaleSeq X₁ (j + 1) : ℝ) ≤ ((scaleSeq X₁ j : ℝ)) ^ ((32 : ℝ) / 10) :=
            hceil.trans hstep
          _ ≤ (X₁ ^ (((32 : ℝ) / 10) ^ (j + 1))) ^ ((32 : ℝ) / 10) :=
            Real.rpow_le_rpow hj_pos.le ih (by norm_num)
          _ = X₁ ^ (((32 : ℝ) / 10) ^ (j + 1 + 1)) := by
            rw [← Real.rpow_mul hX₁_pos.le, ← pow_succ]
  -- Each interval [Y i, (Y i)^3.06] contains at most one index j ∈ Fin (R + 1).
  have huniq : ∀ i : Fin R, ∀ j₁ j₂ : Fin (R + 1),
      (Y i ≤ (scaleSeq X₁ j₁.val : ℝ) ∧ (scaleSeq X₁ j₁.val : ℝ) ≤ (Y i) ^ ((306 : ℝ) / 100)) →
      (Y i ≤ (scaleSeq X₁ j₂.val : ℝ) ∧ (scaleSeq X₁ j₂.val : ℝ) ≤ (Y i) ^ ((306 : ℝ) / 100)) →
      j₁ = j₂ := by
    intro i j₁ j₂ h1 h2
    by_contra hne
    have hlt : j₁.val < j₂.val ∨ j₂.val < j₁.val := lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
    have hstep_gt : ∀ a b : ℕ, a < b →
        Y i ≤ (scaleSeq X₁ a : ℝ) →
        (Y i) ^ ((306 : ℝ) / 100) < (scaleSeq X₁ b : ℝ) := by
      intro a b hab haY
      have ha1 : a + 1 ≤ b := hab
      have hxb : (scaleSeq X₁ (a + 1) : ℝ) ≤ (scaleSeq X₁ b : ℝ) := by
        exact_mod_cast hmono.monotone ha1
      have ha_ge : (2 : ℝ) ^ 10 ≤ (scaleSeq X₁ a : ℝ) := hge a
      have ha_gt1 : (1 : ℝ) < (scaleSeq X₁ a : ℝ) := by linarith [show (1 : ℝ) < (2 : ℝ) ^ 10 by norm_num]
      have hYpos : 0 < Y i := lt_of_lt_of_le zero_lt_one (hY i)
      calc
        (Y i) ^ ((306 : ℝ) / 100) ≤ (scaleSeq X₁ a : ℝ) ^ ((306 : ℝ) / 100) :=
          Real.rpow_le_rpow hYpos.le haY (by norm_num)
        _ < (scaleSeq X₁ a : ℝ) ^ ((31 : ℝ) / 10) :=
          Real.rpow_lt_rpow_of_exponent_lt ha_gt1 (by norm_num)
        _ ≤ (scaleSeq X₁ (a + 1) : ℝ) := Nat.le_ceil _
        _ ≤ (scaleSeq X₁ b : ℝ) := hxb
    rcases hlt with h12 | h21
    · linarith [hstep_gt j₁.val j₂.val h12 h1.1, h2.2]
    · linarith [hstep_gt j₂.val j₁.val h21 h2.1, h1.2]
  -- By pigeonhole (R + 1 indices vs R intervals), some j ∈ Fin (R + 1) misses all R intervals!
  have hex_good : ∃ j : Fin (R + 1),
      ∀ i : Fin R, ¬ (Y i ≤ (scaleSeq X₁ j.val : ℝ) ∧
        (scaleSeq X₁ j.val : ℝ) ≤ (Y i) ^ ((306 : ℝ) / 100)) := by
    by_contra hall_bad
    push Not at hall_bad
    choose f hf using hall_bad
    have hinj : Function.Injective f := by
      intro j₁ j₂ hfeq
      have h2 := hf j₂
      rw [← hfeq] at h2
      exact huniq (f j₁) j₁ j₂ (hf j₁) h2
    have hcard := Fintype.card_le_of_injective f hinj
    simp at hcard
  obtain ⟨j, hj_good⟩ := hex_good
  refine ⟨scaleSeq X₁ j.val, ?_, ?_, hj_good⟩
  · have h0 : X₁ ≤ (scaleSeq X₁ 0 : ℝ) := Nat.le_ceil X₁
    have hm : (scaleSeq X₁ 0 : ℝ) ≤ (scaleSeq X₁ j.val : ℝ) := by
      exact_mod_cast hmono.monotone (Nat.zero_le j.val)
    exact h0.trans hm
  · have hpow_le : ((32 : ℝ) / 10) ^ (j.val + 1) ≤ ((32 : ℝ) / 10) ^ (R + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 32 / 10) (Nat.succ_le_succ (Nat.lt_succ_iff.mp j.isLt))
    exact (hupper j.val).trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hpow_le)

/-- **Eventual `O(X^a)` Stopping-Time Bound:**
Since the `R` exceptional shell bands have a finite maximum rank, `ShellSeparationCovering`
implies an eventual bound `N_T(X) ≤ C * X^a` for all `X ≥ 1`. -/
theorem eventual_bound_of_shell_covering (cov : ShellSeparationCovering) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (N_T X : ℝ) ≤ C * (X : ℝ) ^ cov.a := by
  classical
  have ha_pos : 0 < cov.a := by linarith [cov.ha_gt]
  set M_top : ℕ :=
    Finset.univ.sup (fun i : Fin cov.R => Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)))
  set K_eff : ℕ := max cov.K (M_top + 1)
  have hK_le : cov.K ≤ K_eff := le_max_left _ _
  have hall_good : ∀ k : ℕ, K_eff ≤ k → (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ (cov.a * (k : ℝ)) := by
    intro k hk
    apply cov.hgood k (hK_le.trans hk)
    intro i ⟨_, hle⟩
    have hceil : Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)) ≤ M_top :=
      Finset.le_sup (f := fun i : Fin cov.R => Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)))
        (Finset.mem_univ i)
    have hlt : cov.ρ_band * (cov.leftEnds i : ℝ) < (k : ℝ) := by
      have h1 : cov.ρ_band * (cov.leftEnds i : ℝ) ≤ (Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)) : ℝ) < (k : ℝ) := by
        have : Nat.ceil (cov.ρ_band * (cov.leftEnds i : ℝ)) < k := by
          have : M_top + 1 ≤ K_eff := le_max_right _ _
          omega
        exact_mod_cast this
      linarith
    linarith
  set C : ℝ := (2 : ℝ) ^ K_eff + (1 - (2 : ℝ) ^ (-cov.a))⁻¹
  have hden_pos : 0 < 1 - (2 : ℝ) ^ (-cov.a) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha_pos))
  refine ⟨C, by positivity, ?_⟩
  intro X hX
  have hXr_ge1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXa_ge1 : (1 : ℝ) ≤ (X : ℝ) ^ cov.a := Real.one_le_rpow hXr_ge1 ha_pos.le
  have hN1 : (N_T X : ℝ) ≤ (2 : ℝ) ^ K_eff +
      ∑ k ∈ Finset.Icc K_eff (Nat.log 2 X), (shellNeverDrops k : ℝ) := by
    exact_mod_cast N_T_le_two_pow_add_sum_shells K_eff X
  have hsum :
      ∑ k ∈ Finset.Icc K_eff (Nat.log 2 X), (shellNeverDrops k : ℝ) ≤
        (X : ℝ) ^ cov.a * (1 - (2 : ℝ) ^ (-cov.a))⁻¹ := by
    calc
      ∑ k ∈ Finset.Icc K_eff (Nat.log 2 X), (shellNeverDrops k : ℝ)
        ≤ ∑ k ∈ Finset.Icc K_eff (Nat.log 2 X), (2 : ℝ) ^ (cov.a * (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hall_good k (Finset.mem_Icc.mp hk).1
      _ ≤ ∑ k ∈ Finset.range (Nat.log 2 X + 1), (2 : ℝ) ^ (cov.a * (k : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
          · intro _ _ _; positivity
      _ ≤ (2 : ℝ) ^ (cov.a * (Nat.log 2 X : ℝ)) / (1 - (2 : ℝ) ^ (-cov.a)) :=
          sum_two_rpow_le ha_pos (Nat.log 2 X)
      _ ≤ (X : ℝ) ^ cov.a / (1 - (2 : ℝ) ^ (-cov.a)) := by
          apply div_le_div_of_nonneg_right _ hden_pos.le
          have hpow : (2 : ℝ) ^ (Nat.log 2 X : ℕ) ≤ (X : ℝ) := by
            exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          exact Real.rpow_le_rpow (by positivity) hpow ha_pos.le
      _ = (X : ℝ) ^ cov.a * (1 - (2 : ℝ) ^ (-cov.a))⁻¹ := by ring
  calc
    (N_T X : ℝ) ≤ (2 : ℝ) ^ K_eff + (X : ℝ) ^ cov.a * (1 - (2 : ℝ) ^ (-cov.a))⁻¹ := by
      linarith
    _ ≤ (2 : ℝ) ^ K_eff * (X : ℝ) ^ cov.a + (X : ℝ) ^ cov.a * (1 - (2 : ℝ) ^ (-cov.a))⁻¹ := by
      have : (2 : ℝ) ^ K_eff ≤ (2 : ℝ) ^ K_eff * (X : ℝ) ^ cov.a := by
        calc (2 : ℝ) ^ K_eff = (2 : ℝ) ^ K_eff * 1 := (mul_one _).symm
          _ ≤ (2 : ℝ) ^ K_eff * (X : ℝ) ^ cov.a :=
            mul_le_mul_of_nonneg_left hXa_ge1 (by positivity)
      linarith
    _ = C * (X : ℝ) ^ cov.a := by dsimp [C]; ring

end CollatzTwoWindow
