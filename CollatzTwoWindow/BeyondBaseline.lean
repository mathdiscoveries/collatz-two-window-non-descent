module

public import CollatzTwoWindow.ShortcutCoding
public import CollatzTwoWindow.CollisionReduction
public import CollatzTwoWindow.Certificates
public import CollatzTwoWindow.WideSlackCert
public import CollatzTwoWindow.TightSlackCert

import Mathlib.Tactic

/-!
# Beyond-Baseline Deepening, End-to-End Slice-to-Shell Assembly, and Master Theorems

Closes BOTH explicit trust-boundary gaps documented in baseline `README.md` and formalizes
the structural obstructions, Terras (1976/1979) finite-additivity results, pigeonhole floors,
and scholarly literature comparisons from Paper 1 (`hughes-collatz-two-window.tex`):

1. **Exact Combinatorial & Probabilistic Slice-Assembly Machinery:**
   - `binom_le_two_rpow_crossEntropy`, `crossEntropy_far_algebraic_identity`,
     `card_shell_prefix_suffix_slice`, `card_shell_prefix_suffix_slice_le_rpow`,
     `card_residue_menu_le`, `collisionCount_eq_near_add_far`,
     `card_farCollisions_slice_le`, `card_nearCollisions_slice_le`.
2. **Unconditional All-Shell & High-Product Tail Bounds + Good-Shell Assembly:**
   - `twoWindowSurvivors`, `shellNeverDrops_le_twoWindowSurvivors`,
     `all_shell_twoWindowSurvivors_le`, `all_shell_neverDrops_le`,
     `high_product_tail_card_le`, `HasWrapSeparation`,
     `wrap_separation_failure_witness`, `good_shell_twoWindowSurvivors_le`.
3. **End-to-End Pure-Kernel Master Theorems (Parameterized SOLELY by `ThreePlaceSubspaceHypothesis`):**
   - `collatz_two_window_wide_0945_covering` & `collatz_two_window_wide_0945_master`
     (`a = 0.945`, `σ = 10^{-4}`, `K = 2^{40}`, `N_T(X) ≤ 5 X^{0.945}` outside `R` bands,
     good scale in every `[X₁, X₁^{3.2^{R+1}}]`, and eventual `N_T(X) ≤ C X^{0.945}`).
   - `collatz_two_window_tight_094476_covering` & `collatz_two_window_tight_094476_master`
     (`a = 0.94476`, `σ = 10^{-7}`, `K = 2^{40}`, using our pure-kernel 401-leaf tight BSP
     certificate `tight_slack_005524_uniform_bound`!).
4. **Structural Obstructions, Terras (1976/1979), & Scholar-Verified Comparisons:**
   - `coalescence_8k_plus_4_5` & `shift_one_autocorrelation_lower` (`G_k(1) ≥ u (1 + u)^{k - 3}`),
   - `collisionCount_ge_card`, `cauchy_schwarz_self_collision_floor`, `lagarias_half_entropy_bounds`,
   - `terras_1979_finite_additivity`, `terras_1976_tableA_k10`, `shell_k10_exact_counts`,
   - `pigeonhole_mod_two_pow`, `pigeonhole_floor_wide_tight_certs`, `tight_pigeonhole_dies_at_300M`,
   - `dyadic_subgroup_obstruction_cert`,
   - `nashida_gain_ratio_gt_88M`, `schlickewei_1990_vs_1992_eq`,
     `evertse_1996_line_counts`, `evertse_ferretti_n3_vs_n2_ratio`.
-/

@[expose] public section

namespace CollatzTwoWindow

/-! ## 1. Exact Combinatorial & Probabilistic Slice-Assembly Building Blocks -/

/-- For `z ∈ (0, 1)`, `2^(-crossEntropy a j z) = z^j * (1 - z)^(a - j)` (for integer counts). -/
private lemma rpow_neg_crossEntropy_nat {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) {n s : ℕ} (hsn : s ≤ n) :
    (2 : ℝ) ^ (-crossEntropy (n : ℝ) (s : ℝ) z) = z ^ s * (1 - z) ^ (n - s) := by
  have h1z : 0 < 1 - z := sub_pos.mpr hz1
  have hsub : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := Nat.cast_sub hsn
  unfold crossEntropy
  have hexp :
      -((s : ℝ) * -Real.logb 2 z + ((n : ℝ) - (s : ℝ)) * -Real.logb 2 (1 - z)) =
        (s : ℝ) * Real.logb 2 z + ((n - s : ℕ) : ℝ) * Real.logb 2 (1 - z) := by
    rw [hsub]; ring
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    mul_comm (s : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) hz0, Real.rpow_natCast,
    mul_comm ((n - s : ℕ) : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) h1z, Real.rpow_natCast]

/-- Exact binomial cross-entropy upper bound: `C(n, s) ≤ 2^{B(n, s; z)}` for all `z ∈ (0, 1)`. -/
theorem binom_le_two_rpow_crossEntropy {n s : ℕ} (hsn : s ≤ n) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    (Nat.choose n s : ℝ) ≤ (2 : ℝ) ^ crossEntropy (n : ℝ) (s : ℝ) z := by
  have h1z : 0 < 1 - z := sub_pos.mpr hz1
  have hterm : (Nat.choose n s : ℝ) * (z ^ s * (1 - z) ^ (n - s)) ≤ 1 := by
    have hsum : (z + (1 - z)) ^ n = 1 := by simp
    rw [add_pow] at hsum
    have hmem : s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hsn)
    have hle := Finset.single_le_sum
      (f := fun m => z ^ m * (1 - z) ^ (n - m) * (Nat.choose n m : ℝ))
      (fun m _ => by positivity) hmem
    linarith [hsum, hle]
  have hpos : 0 < z ^ s * (1 - z) ^ (n - s) := by positivity
  rw [← rpow_neg_crossEntropy_nat hz0 hz1 hsn] at hterm hpos
  have hinv := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (crossEntropy (n : ℝ) (s : ℝ) z)
  rw [hinv] at hterm
  have h2pos : 0 < (2 : ℝ) ^ crossEntropy (n : ℝ) (s : ℝ) z := by positivity
  have hmul := mul_le_mul_of_nonneg_right hterm h2pos.le
  rw [mul_assoc, inv_mul_cancel₀ h2pos.ne', mul_one, one_mul] at hmul
  exact hmul

/-- Exact algebraic far-pair cross-entropy identity (Paper 1 Section 3.4):
`B(L, J; q) + 2 t * log_2(λ(q)) = 2 t + B(L - 2 t, J - t; q)` for all `q ∈ (0, 1)`. -/
theorem crossEntropy_far_algebraic_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (L J t : ℝ) :
    crossEntropy L J q + (2 * t) * Real.logb 2 (couplingLambda q) =
      2 * t + crossEntropy (L - 2 * t) (J - t) q := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hlam : Real.logb 2 (couplingLambda q) =
      1 + (Real.logb 2 q + Real.logb 2 (1 - q)) / 2 := by
    unfold couplingLambda Real.logb
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (mul_pos hq0 h1q)).ne',
      Real.log_sqrt (mul_pos hq0 h1q).le,
      Real.log_mul hq0.ne' h1q.ne']
    field_simp [hlog2]
  unfold crossEntropy
  rw [hlam]
  ring

/-- Exact cardinality of the prefix-suffix weight slice on dyadic shell `[2^k, 2^(k+1))`:
`#{n ∈ [2^k, 2^(k+1)) : s_r(n) = s_r ∧ s_{r..k}(n) = j} = C(r, s_r) * C(k - r, j)`. -/
theorem card_shell_prefix_suffix_slice {k r s_r j : ℕ} (hrk : r ≤ k) :
    ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun n => oddCount r n = s_r ∧ suffixOddCount r (k - r) n = j)).card =
      Nat.choose r s_r * Nat.choose (k - r) j := by
  have hbij := parityWord_bijective_shell k
  set L := k - r
  have hrL : r + L = k := Nat.add_sub_of_le hrk
  let eShell : Fin (2 ^ k) ≃ (Fin k → Bool) := Equiv.ofBijective _ hbij
  let splitWord : (Fin k → Bool) ≃ (Fin r → Bool) × (Fin L → Bool) :=
    { toFun := fun w =>
        (fun i => w ⟨i.val, lt_of_lt_of_le i.isLt hrk⟩,
         fun i => w ⟨r + i.val, by omega⟩)
      invFun := fun p i =>
        if h : i.val < r then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - r, by omega⟩
      left_inv := fun w => by
        funext i
        dsimp only
        split_ifs with h
        · rfl
        · congr 1; apply Fin.ext; dsimp only; omega
      right_inv := fun ⟨u, v⟩ => by
        apply Prod.ext
        · funext i; dsimp only; simp [i.isLt]
        · funext i; dsimp only
          have hnot : ¬ (r + i.val < r) := by omega
          simp only [hnot, ↓reduceDIte]
          congr 1; apply Fin.ext; dsimp only; omega }
  have hwt_pref : ∀ n : ℕ, oddCount r n =
      wordWeight (fun i : Fin r => parityWord k n ⟨i.val, lt_of_lt_of_le i.isLt hrk⟩) := by
    intro n
    rw [oddCount_eq_card_filter]
    rfl
  have hwt_suf : ∀ n : ℕ, suffixOddCount r L n =
      wordWeight (fun i : Fin L => parityWord k n ⟨r + i.val, by omega⟩) := by
    intro n
    unfold suffixOddCount wordWeight
    rw [oddCount_eq_card_filter]
    congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, parityWord,
      ← Function.iterate_add_apply, Nat.add_comm r]
  have hchoose_words : ∀ (m w : ℕ),
      (Finset.univ.filter (fun u : Fin m → Bool => wordWeight u = w)).card = Nat.choose m w := by
    intro m w
    have hpowc : Nat.choose m w = ((Finset.univ : Finset (Fin m)).powersetCard w).card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hpowc]
    apply Finset.card_bij (fun u _ => Finset.univ.filter (fun i : Fin m => u i = true))
    · intro u hu
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hu).2⟩
    · intro u₁ _ u₂ _ heq
      funext i
      have hiff : (i ∈ Finset.univ.filter (fun j : Fin m => u₁ j = true)) ↔
          (i ∈ Finset.univ.filter (fun j : Fin m => u₂ j = true)) := by rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiff
      cases hu1 : u₁ i <;> cases hu2 : u₂ i <;> simp [hu1, hu2] at hiff ⊢
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold wordWeight
        convert hS.2
        ext i; simp
      · ext i; simp
  rw [← hchoose_words r s_r, ← hchoose_words L j, ← Finset.card_product]
  apply Finset.card_bij
    (fun (n : ℕ) (hn : n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => oddCount r n = s_r ∧ suffixOddCount r L n = j)) =>
      splitWord (parityWord k n))
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩
    · change wordWeight (fun i : Fin r => parityWord k n ⟨i.val, lt_of_lt_of_le i.isLt hrk⟩) = s_r
      rw [← hwt_pref n]; exact hn.2.1
    · change wordWeight (fun i : Fin L => parityWord k n ⟨r + i.val, by omega⟩) = j
      rw [← hwt_suf n]; exact hn.2.2
  · intro n₁ hn₁ n₂ hn₂ heq
    have hw : parityWord k n₁ = parityWord k n₂ := splitWord.injective heq
    have hmod := mod_two_pow_eq_of_parityWord_eq k hw
    have h1 := Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1
    have h2p : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hm1 : n₁ % 2 ^ k = n₁ - 2 ^ k := by
      have hdecomp : n₁ = (n₁ - 2 ^ k) + 1 * 2 ^ k := by omega
      conv_lhs => rw [hdecomp]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hm2 : n₂ % 2 ^ k = n₂ - 2 ^ k := by
      have hdecomp : n₂ = (n₂ - 2 ^ k) + 1 * 2 ^ k := by omega
      conv_lhs => rw [hdecomp]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro uv huv
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at huv
    set w := splitWord.symm uv
    set idx := eShell.symm w
    have hpw : parityWord k (2 ^ k + idx.val) = w := eShell.apply_symm_apply w
    refine ⟨2 ^ k + idx.val, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ico]
      have h2p : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      refine ⟨⟨by omega, by have := idx.isLt; omega⟩, ?_, ?_⟩
      · rw [hwt_pref, hpw]
        have := congrArg Prod.fst (splitWord.apply_symm_apply uv)
        simpa [splitWord, w] using (congrArg wordWeight this).trans huv.1.2
      · rw [hwt_suf, hpw]
        have := congrArg Prod.snd (splitWord.apply_symm_apply uv)
        simpa [splitWord, w] using (congrArg wordWeight this).trans huv.2.2
    · rw [hpw]; exact splitWord.apply_symm_apply uv

/-- Direct cross-entropy upper bound for any prefix-suffix slice on `[2^k, 2^(k+1))`. -/
theorem card_shell_prefix_suffix_slice_le_rpow {k r s_r j : ℕ} (hrk : r ≤ k)
    (hsr : s_r ≤ r) (hj : j ≤ k - r) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun n => oddCount r n = s_r ∧ suffixOddCount r (k - r) n = j)).card : ℝ) ≤
      (2 : ℝ) ^ (crossEntropy (r : ℝ) (s_r : ℝ) x + crossEntropy ((k - r : ℕ) : ℝ) (j : ℝ) y) := by
  rw [card_shell_prefix_suffix_slice hrk, Nat.cast_mul, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul (binom_le_two_rpow_crossEntropy hsr hx0 hx1)
    (binom_le_two_rpow_crossEntropy hj hy0 hy1) (Nat.cast_nonneg _) (by positivity)

/-- Monotone tilted-mass bound on the set of residues modulo `2^m` with `oddCount m y ≥ s₀`
(used for both the second-window residue menu `Z_s` and the all-shell / high-product bounds). -/
theorem card_residue_menu_le {m : ℕ} {s₀ z : ℝ} (hz_half : (1 : ℝ) / 2 ≤ z) (hz1 : z < 1) :
    (((Finset.range (2 ^ m)).filter (fun y => s₀ ≤ (oddCount m y : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ crossEntropy (m : ℝ) s₀ z := by
  have hz0 : 0 < z := by linarith
  have h1z : 0 < 1 - z := sub_pos.mpr hz1
  have hlog_mono : -Real.logb 2 z ≤ -Real.logb 2 (1 - z) := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) h1z (by linarith : 1 - z ≤ z)
    linarith
  set M : ℝ := (2 : ℝ) ^ (-crossEntropy (m : ℝ) s₀ z)
  have hM_pos : 0 < M := by positivity
  have hAmin : ∀ y ∈ (Finset.range (2 ^ m)).filter (fun y => s₀ ≤ (oddCount m y : ℝ)),
      M ≤ tiltedMass z m y := by
    intro y hy
    have hs₀ : s₀ ≤ (oddCount m y : ℝ) := (Finset.mem_filter.mp hy).2
    have hsm : oddCount m y ≤ m := oddCount_le m y
    have htm : tiltedMass z m y = (2 : ℝ) ^ (-crossEntropy (m : ℝ) (oddCount m y : ℝ) z) :=
      (rpow_neg_crossEntropy_nat hz0 hz1 hsm).symm
    rw [htm]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    unfold crossEntropy
    have hdiff : 0 ≤ ((oddCount m y : ℝ) - s₀) * ((-Real.logb 2 (1 - z)) - (-Real.logb 2 z)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hcard := card_le_inv_of_tiltedMass_ge hz0.le hz1.le hM_pos m
    ((Finset.range (2 ^ m)).filter (fun y => s₀ ≤ (oddCount m y : ℝ)))
    (Finset.filter_subset _ _) hAmin
  have hMinv : M⁻¹ = (2 : ℝ) ^ crossEntropy (m : ℝ) s₀ z := by
    dsimp [M]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rwa [hMinv] at hcard

/-- Ordered near collisions on `A` (`suffixHammingDist r L n n' < H`). -/
def nearCollisions {β : Type*} [DecidableEq β] (A : Finset ℕ) (f : ℕ → β) (r L H : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => f p.1 = f p.2 ∧ suffixHammingDist r L p.1 p.2 < H)).card

/-- Ordered far collisions on `A` (`H ≤ suffixHammingDist r L n n'`). -/
def farCollisions {β : Type*} [DecidableEq β] (A : Finset ℕ) (f : ℕ → β) (r L H : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => f p.1 = f p.2 ∧ H ≤ suffixHammingDist r L p.1 p.2)).card

/-- Exact partition of ordered collisions into near pairs and far pairs. -/
theorem collisionCount_eq_near_add_far {β : Type*} [DecidableEq β]
    (A : Finset ℕ) (f : ℕ → β) (r L H : ℕ) :
    collisionCount A f = nearCollisions A f r L H + farCollisions A f r L H := by
  unfold collisionCount nearCollisions farCollisions
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
    · intro ⟨hp, hfeq⟩
      by_cases hlt : suffixHammingDist r L p.1 p.2 < H
      · exact Or.inl ⟨hp, hfeq, hlt⟩
      · exact Or.inr ⟨hp, hfeq, Nat.le_of_not_lt hlt⟩
    · rintro (⟨hp, hfeq, _⟩ | ⟨hp, hfeq, _⟩) <;> exact ⟨hp, hfeq⟩
  · rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2; omega

/-- Helper: `suffixOddCount r L n` and `suffixHammingDist r L n n'` are invariant modulo `2^(r + L)`. -/
private lemma suffix_mod_invariance (r L n₁ n₂ q₁ q₂ : ℕ) :
    suffixOddCount r L (n₁ + q₁ * 2 ^ (r + L)) = suffixOddCount r L n₁ ∧
    suffixHammingDist r L (n₁ + q₁ * 2 ^ (r + L)) (n₂ + q₂ * 2 ^ (r + L)) =
      suffixHammingDist r L n₁ n₂ := by
  have h1 : n₁ + q₁ * 2 ^ (r + L) = n₁ + (q₁ * 2 ^ L) * 2 ^ r := by rw [pow_add]; ring
  have h2 : n₂ + q₂ * 2 ^ (r + L) = n₂ + (q₂ * 2 ^ L) * 2 ^ r := by rw [pow_add]; ring
  have hT1 : T^[r] (n₁ + q₁ * 2 ^ (r + L)) = T^[r] n₁ + (q₁ * 3 ^ oddCount r n₁) * 2 ^ L := by
    rw [h1, (iterate_add_two_pow_mul r n₁ (q₁ * 2 ^ L)).1]; ring
  have hT2 : T^[r] (n₂ + q₂ * 2 ^ (r + L)) = T^[r] n₂ + (q₂ * 3 ^ oddCount r n₂) * 2 ^ L := by
    rw [h2, (iterate_add_two_pow_mul r n₂ (q₂ * 2 ^ L)).1]; ring
  constructor
  · unfold suffixOddCount; rw [hT1]; exact oddCount_add_two_pow_mul L (T^[r] n₁) _
  · unfold suffixHammingDist; rw [hT1, hT2]; exact hammingDist_add_two_pow_mul L (T^[r] n₁) (T^[r] n₂) _ _

/-- **Exact Per-Slice Far-Pair Bound under Prefix-Residue Shift Injectivity:**
If every pair of prefix residues modulo `2^r` determines at most one integer shift on colliding
pairs of a fixed-composition slice `A ⊆ [2^k, 2^(k+1))`, then for any `q ∈ (0, 1)`,
`farCollisions A f r L H ≤ C(r, s_r)^2 * 2^{B(L, j; q)} * λ(q)^H`. -/
theorem card_farCollisions_slice_le {β : Type*} [DecidableEq β]
    {k r L s_r j H : ℕ} (hrL : r + L = k) (hjL : j ≤ L)
    {A : Finset ℕ} (hAsub : A ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)))
    (hAsr : ∀ n ∈ A, oddCount r n = s_r)
    (hAj : ∀ n ∈ A, suffixOddCount r L n = j)
    (f : ℕ → β)
    (hsep : ∀ n₁ ∈ A, ∀ n₁' ∈ A, ∀ n₂ ∈ A, ∀ n₂' ∈ A,
      f n₁ = f n₁' → f n₂ = f n₂' →
      n₁ % 2 ^ r = n₂ % 2 ^ r → n₁' % 2 ^ r = n₂' % 2 ^ r →
      (n₁' : ℤ) - (n₁ : ℤ) = (n₂' : ℤ) - (n₂ : ℤ))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (farCollisions A f r L H : ℝ) ≤
      (Nat.choose r s_r : ℝ) ^ 2 * (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q *
        (couplingLambda q) ^ H := by
  classical
  set P : Finset ℕ := (Finset.range (2 ^ r)).filter (fun a => oddCount r a = s_r)
  have hPcard : P.card = Nat.choose r s_r := by
    have hbij := parityWord_bijective_fin r
    let eR : Fin (2 ^ r) ≃ (Fin r → Bool) := Equiv.ofBijective _ hbij
    have hpowc : Nat.choose r s_r = ((Finset.univ : Finset (Fin r)).powersetCard s_r).card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hpowc]
    apply Finset.card_bij (fun a _ => Finset.univ.filter (fun i : Fin r => parityWord r a i = true))
    · intro a ha
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← oddCount_eq_card_filter]; exact (Finset.mem_filter.mp ha).2
    · intro a₁ ha₁ a₂ ha₂ heq
      have hpw : parityWord r a₁ = parityWord r a₂ := by
        funext i
        have hiff : (i ∈ Finset.univ.filter (fun l : Fin r => parityWord r a₁ l = true)) ↔
            (i ∈ Finset.univ.filter (fun l : Fin r => parityWord r a₂ l = true)) := by rw [heq]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiff
        cases h1 : parityWord r a₁ i <;> cases h2 : parityWord r a₂ i <;> simp [h1, h2] at hiff ⊢
      have hm := mod_two_pow_eq_of_parityWord_eq r hpw
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1),
        Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1)] at hm
      exact hm
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      set w : Fin r → Bool := fun i => decide (i ∈ S)
      set idx := eR.symm w
      have hpw : parityWord r idx.val = w := eR.apply_symm_apply w
      refine ⟨idx.val, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨idx.isLt, ?_⟩
        rw [oddCount_eq_card_filter, hpw]
        convert hS.2; ext i; simp [w]
      · rw [hpw]; ext i; simp [w]
  set FarSet := (A ×ˢ A).filter (fun p => f p.1 = f p.2 ∧ H ≤ suffixHammingDist r L p.1 p.2)
  have hpart :
      FarSet = (P ×ˢ P).biUnion (fun ab =>
        FarSet.filter (fun p => p.1 % 2 ^ r = ab.1 ∧ p.2 % 2 ^ r = ab.2)) := by
    ext ⟨n, n'⟩
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      P, FarSet]
    constructor
    · intro h
      refine ⟨(n % 2 ^ r, n' % 2 ^ r), ⟨⟨Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)), ?_⟩,
        ⟨Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)), ?_⟩⟩, h, rfl, rfl⟩
      · rw [oddCount_mod]; exact hAsr n h.1.1
      · rw [oddCount_mod]; exact hAsr n' h.1.2
    · rintro ⟨_, _, h, _, _⟩; exact h
  have hfib_bound : ∀ ab ∈ P ×ˢ P,
      ((FarSet.filter (fun p => p.1 % 2 ^ r = ab.1 ∧ p.2 % 2 ^ r = ab.2)).card : ℝ) ≤
        (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q * (couplingLambda q) ^ H := by
    intro ⟨a, a'⟩ hab
    set F_ab := FarSet.filter (fun p => p.1 % 2 ^ r = a ∧ p.2 % 2 ^ r = a')
    by_cases hemp : F_ab.Nonempty
    · obtain ⟨⟨n₀, n₀'⟩, h0⟩ := hemp
      have h0' := Finset.mem_filter.mp h0
      have h0F := Finset.mem_filter.mp h0'.1
      have h0A1 : n₀ ∈ A := (Finset.mem_product.mp h0F.1).1
      have h0A2 : n₀' ∈ A := (Finset.mem_product.mp h0F.1).2
      set dInt : ℤ := (n₀' : ℤ) - (n₀ : ℤ)
      set dNat : ℕ := (dInt % (2 ^ k : ℤ)).toNat
      have h2k_pos : (0 : ℤ) < (2 ^ k : ℤ) := by positivity
      have hdNat_mod : (dNat : ℤ) ≡ dInt [ZMOD (2 ^ k : ℤ)] := by
        have hnn : 0 ≤ dInt % (2 ^ k : ℤ) := Int.emod_nonneg dInt h2k_pos.ne'
        change (dNat : ℤ) % (2 ^ k : ℤ) = dInt % (2 ^ k : ℤ)
        rw [Int.toNat_of_nonneg hnn, Int.emod_emod]
      -- Map each pair (n, n') ∈ F_ab injectively into u ∈ range (2^L) via u = (n - 2^k) / 2^r.
      set U_ab : Finset ℕ := (Finset.range (2 ^ L)).filter
        (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + dNat) ∧
          suffixOddCount r L (a + u * 2 ^ r) = j ∧
          suffixOddCount r L (a + u * 2 ^ r + dNat) = j)
      have hcard_le_U : F_ab.card ≤ U_ab.card := by
        have hmap_sub : F_ab.image (fun p => (p.1 - 2 ^ k) / 2 ^ r) ⊆ U_ab := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨⟨n, n'⟩, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hpF := Finset.mem_filter.mp hp'.1
          have hnA : n ∈ A := (Finset.mem_product.mp hpF.1).1
          have hn'A : n' ∈ A := (Finset.mem_product.mp hpF.1).2
          have hnIco := Finset.mem_Ico.mp (hAsub hnA)
          have hn'Ico := Finset.mem_Ico.mp (hAsub hn'A)
          have h2p : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          have hshift : (n' : ℤ) - (n : ℤ) = dInt :=
            hsep n hnA n' hn'A n₀ h0A1 n₀' h0A2 hpF.2.1 h0F.2.1
              (hp'.2.1.trans h0'.2.1.symm) (hp'.2.2.trans h0'.2.2.symm)
          have h2r_dvd_2k : 2 ^ r ∣ 2 ^ k := by rw [← hrL, pow_add]; exact dvd_mul_right _ _
          have hn_rem : (n - 2 ^ k) % 2 ^ r = a := by
            have h1 : n = (n - 2 ^ k) + 2 ^ k := by omega
            have h2 : n % 2 ^ r = (n - 2 ^ k) % 2 ^ r := by
              conv_lhs => rw [h1]
              rcases h2r_dvd_2k with ⟨c, hc⟩
              rw [hc, mul_comm (2 ^ r) c, Nat.add_mul_mod_self_right]
            exact h2.symm.trans hp'.2.1
          set uVal := (n - 2 ^ k) / 2 ^ r
          have hu_lt : uVal < 2 ^ L := by
            apply Nat.div_lt_of_lt_mul
            rw [← pow_add, hrL]; omega
          have hn_eq : n = a + uVal * 2 ^ r + 1 * 2 ^ k := by
            have hdm : uVal * 2 ^ r + a = n - 2 ^ k := by
              dsimp [uVal]; rw [mul_comm, ← hn_rem]; exact Nat.div_add_mod (n - 2 ^ k) (2 ^ r)
            omega
          -- Express n' and a + uVal * 2^r + dNat as congruent modulo 2^k:
          have hcongr : (a + uVal * 2 ^ r + dNat : ℤ) % (2 ^ k : ℤ) = (n' : ℤ) % (2 ^ k : ℤ) := by
            have hstep1 : (n' : ℤ) = (n : ℤ) + dInt := by linarith
            have hstep2 : (n : ℤ) = (a + uVal * 2 ^ r : ℤ) + (2 ^ k : ℤ) := by
              have h1 : (n : ℤ) = ((a + uVal * 2 ^ r + 1 * 2 ^ k : ℕ) : ℤ) := congrArg Nat.cast hn_eq
              push_cast at h1; linarith
            rw [hstep1, hstep2]
            have := hdNat_mod
            change (dNat : ℤ) % (2 ^ k : ℤ) = dInt % (2 ^ k : ℤ) at this
            rw [Int.add_emod, this, ← Int.add_emod]
            have heq : (a + uVal * 2 ^ r : ℤ) + (2 ^ k : ℤ) + dInt =
                ((a + uVal * 2 ^ r : ℤ) + dInt) + (2 ^ k : ℤ) := by ring
            rw [heq, Int.add_emod_right]
          have hnat_mod : (a + uVal * 2 ^ r + dNat) % 2 ^ k = n' % 2 ^ k := by
            exact_mod_cast hcongr
          set base1 := a + uVal * 2 ^ r
          set base2 := a + uVal * 2 ^ r + dNat
          have hinv1 : suffixOddCount r L n = suffixOddCount r L base1 := by
            rw [hn_eq, ← hrL]; exact (suffix_mod_invariance r L base1 0 1 0).1
          have hinv2 : suffixOddCount r L base2 = suffixOddCount r L n' := by
            have h1 : suffixOddCount r L base2 = suffixOddCount r L (base2 % 2 ^ k) := by
              have h := (suffix_mod_invariance r L (base2 % 2 ^ k) 0 (base2 / 2 ^ k) 0).1
              rw [hrL, mul_comm (base2 / 2 ^ k), Nat.mod_add_div] at h
              exact h
            have h2 : suffixOddCount r L n' = suffixOddCount r L (n' % 2 ^ k) := by
              have h := (suffix_mod_invariance r L (n' % 2 ^ k) 0 (n' / 2 ^ k) 0).1
              rw [hrL, mul_comm (n' / 2 ^ k), Nat.mod_add_div] at h
              exact h
            rw [h1, h2, hnat_mod]
          have hinvH : suffixHammingDist r L base1 base2 = suffixHammingDist r L n n' := by
            have h1 : suffixHammingDist r L base1 base2 =
                suffixHammingDist r L base1 (base2 % 2 ^ k) := by
              have h := (suffix_mod_invariance r L base1 (base2 % 2 ^ k) 0 (base2 / 2 ^ k)).2
              rw [hrL, zero_mul, add_zero, mul_comm (base2 / 2 ^ k), Nat.mod_add_div] at h
              exact h
            have h2 : suffixHammingDist r L n n' =
                suffixHammingDist r L base1 (n' % 2 ^ k) := by
              have h := (suffix_mod_invariance r L base1 (n' % 2 ^ k) 1 (n' / 2 ^ k)).2
              rw [hrL, ← hn_eq, mul_comm (n' / 2 ^ k), Nat.mod_add_div] at h
              exact h
            rw [h1, h2, hnat_mod]
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨hu_lt, ?_, ?_, ?_⟩
          · rw [hinvH]; exact hpF.2.2
          · rw [← hinv1]; exact hAj n hnA
          · rw [hinv2]; exact hAj n' hn'A
        have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 - 2 ^ k) / 2 ^ r) (F_ab : Set (ℕ × ℕ)) := by
          intro ⟨n₁, n₁'⟩ h1 ⟨n₂, n₂'⟩ h2 hdiv
          dsimp only at hdiv
          have h1' := Finset.mem_filter.mp h1
          have h2' := Finset.mem_filter.mp h2
          have h1F := Finset.mem_filter.mp h1'.1
          have h2F := Finset.mem_filter.mp h2'.1
          have hn1A : n₁ ∈ A := (Finset.mem_product.mp h1F.1).1
          have hn1'A : n₁' ∈ A := (Finset.mem_product.mp h1F.1).2
          have hn2A : n₂ ∈ A := (Finset.mem_product.mp h2F.1).1
          have hn2'A : n₂' ∈ A := (Finset.mem_product.mp h2F.1).2
          have h2r_dvd_2k : 2 ^ r ∣ 2 ^ k := by rw [← hrL, pow_add]; exact dvd_mul_right _ _
          have hn1_rem : (n₁ - 2 ^ k) % 2 ^ r = (n₂ - 2 ^ k) % 2 ^ r := by
            have hge1 := (Finset.mem_Ico.mp (hAsub hn1A)).1
            have hge2 := (Finset.mem_Ico.mp (hAsub hn2A)).1
            rcases h2r_dvd_2k with ⟨c, hc⟩
            have hc' : c * 2 ^ r = 2 ^ k := by rw [mul_comm, ← hc]
            have e1 : n₁ % 2 ^ r = (n₁ - 2 ^ k) % 2 ^ r := by
              conv_lhs => rw [show n₁ = (n₁ - 2 ^ k) + c * 2 ^ r by omega]
              exact Nat.add_mul_mod_self_right _ _ _
            have e2 : n₂ % 2 ^ r = (n₂ - 2 ^ k) % 2 ^ r := by
              conv_lhs => rw [show n₂ = (n₂ - 2 ^ k) + c * 2 ^ r by omega]
              exact Nat.add_mul_mod_self_right _ _ _
            rw [← e1, ← e2, h1'.2.1, h2'.2.1]
          have hn1_eq : n₁ = n₂ := by
            have hge1 := (Finset.mem_Ico.mp (hAsub hn1A)).1
            have hge2 := (Finset.mem_Ico.mp (hAsub hn2A)).1
            have d1 := Nat.div_add_mod (n₁ - 2 ^ k) (2 ^ r)
            have d2 := Nat.div_add_mod (n₂ - 2 ^ k) (2 ^ r)
            rw [hdiv, hn1_rem] at d1
            omega
          have hsh : (n₁' : ℤ) - (n₁ : ℤ) = (n₂' : ℤ) - (n₂ : ℤ) :=
            hsep n₁ hn1A n₁' hn1'A n₂ hn2A n₂' hn2'A h1F.2.1 h2F.2.1
              (h1'.2.1.trans h2'.2.1.symm) (h1'.2.2.trans h2'.2.2.symm)
          have hn1'_eq : n₁' = n₂' := by omega
          exact Prod.ext hn1_eq hn1'_eq
        calc F_ab.card = (F_ab.image (fun p => (p.1 - 2 ^ k) / 2 ^ r)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ U_ab.card := Finset.card_le_card hmap_sub
      -- Apply suffix_shifted_bernoulli_far_bound on U_ab!
      set M : ℝ := (2 : ℝ) ^ (-crossEntropy (L : ℝ) (j : ℝ) q)
      have hM_pos : 0 < M := by positivity
      have hU_sum :
          (U_ab.card : ℝ) * M ≤ (couplingLambda q) ^ H := by
        have hstep1 :
            (U_ab.card : ℝ) * M =
              ∑ u ∈ U_ab, Real.sqrt (suffixTiltedMass q r L (a + u * 2 ^ r) *
                suffixTiltedMass q r L (a + u * 2 ^ r + dNat)) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_congr rfl
          intro u hu
          have hu' := (Finset.mem_filter.mp hu).2
          have h1 : suffixTiltedMass q r L (a + u * 2 ^ r) = M := by
            unfold suffixTiltedMass tiltedMass
            change q ^ suffixOddCount r L (a + u * 2 ^ r) *
              (1 - q) ^ (L - suffixOddCount r L (a + u * 2 ^ r)) = M
            dsimp [M]; rw [hu'.2.1, rpow_neg_crossEntropy_nat hq0 hq1 hjL]
          have h2 : suffixTiltedMass q r L (a + u * 2 ^ r + dNat) = M := by
            unfold suffixTiltedMass tiltedMass
            change q ^ suffixOddCount r L (a + u * 2 ^ r + dNat) *
              (1 - q) ^ (L - suffixOddCount r L (a + u * 2 ^ r + dNat)) = M
            dsimp [M]; rw [hu'.2.2, rpow_neg_crossEntropy_nat hq0 hq1 hjL]
          rw [h1, h2, Real.sqrt_mul_self hM_pos.le]
        rw [hstep1]
        have hsub_far : U_ab ⊆ (Finset.range (2 ^ L)).filter
            (fun u => H ≤ suffixHammingDist r L (a + u * 2 ^ r) (a + u * 2 ^ r + dNat)) := by
          intro u hu
          rw [Finset.mem_filter] at hu ⊢
          exact ⟨hu.1, hu.2.1⟩
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_far (fun _ _ _ => Real.sqrt_nonneg _)).trans
          (suffix_shifted_bernoulli_far_bound hq0 hq1 r L a dNat H)
      have hU_le : (U_ab.card : ℝ) ≤ (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q * (couplingLambda q) ^ H := by
        have hMinv : M⁻¹ = (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q := by
          dsimp [M]; rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
        have hmul := mul_le_mul_of_nonneg_left hU_sum (inv_nonneg.mpr hM_pos.le)
        have hcancel : M⁻¹ * ((U_ab.card : ℝ) * M) = (U_ab.card : ℝ) := by
          rw [mul_comm (U_ab.card : ℝ) M, ← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
        rw [hcancel, hMinv] at hmul
        exact hmul
      exact le_trans (by exact_mod_cast hcard_le_U) hU_le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
      have hlam_pos : 0 < couplingLambda q := couplingLambda_pos hq0 hq1
      positivity
  have hFar_nat : farCollisions A f r L H ≤
      ∑ ab ∈ P ×ˢ P, (FarSet.filter (fun p => p.1 % 2 ^ r = ab.1 ∧ p.2 % 2 ^ r = ab.2)).card := by
    change FarSet.card ≤ _
    conv_lhs => rw [hpart]
    exact Finset.card_biUnion_le
  calc
    (farCollisions A f r L H : ℝ)
      ≤ ∑ ab ∈ P ×ˢ P,
          ((FarSet.filter (fun p => p.1 % 2 ^ r = ab.1 ∧ p.2 % 2 ^ r = ab.2)).card : ℝ) := by
        exact_mod_cast hFar_nat
    _ ≤ ∑ _ab ∈ P ×ˢ P, ((2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q * (couplingLambda q) ^ H) :=
        Finset.sum_le_sum hfib_bound
    _ = ((P ×ˢ P).card : ℝ) * ((2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q * (couplingLambda q) ^ H) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose r s_r : ℝ) ^ 2 * (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q *
          (couplingLambda q) ^ H := by
        rw [Finset.card_product, hPcard, Nat.cast_mul]; ring

/-- Helper: `affineOffset L n` depends only on `parityWord L n`. -/
private lemma affineOffset_eq_of_parityWord_eq {L a b : ℕ}
    (hpw : parityWord L a = parityWord L b) : affineOffset L a = affineOffset L b := by
  have hmod := mod_two_pow_eq_of_parityWord_eq L hpw
  have h1 : affineOffset L a = affineOffset L (a % 2 ^ L) := by
    have := affineOffset_add_two_pow_mul L (a % 2 ^ L) (a / 2 ^ L)
    rw [show a % 2 ^ L + a / 2 ^ L * 2 ^ L = a by rw [mul_comm]; exact Nat.mod_add_div a (2 ^ L)] at this
    exact this
  have h2 : affineOffset L b = affineOffset L (b % 2 ^ L) := by
    have := affineOffset_add_two_pow_mul L (b % 2 ^ L) (b / 2 ^ L)
    rw [show b % 2 ^ L + b / 2 ^ L * 2 ^ L = b by rw [mul_comm]; exact Nat.mod_add_div b (2 ^ L)] at this
    exact this
  rw [h1, h2, hmod]

/-- **Exact Per-Slice Near-Pair Bound (Close-Pair Constant-Weight Inversion):**
Combines `card_same_weight_hamming_sphere` (`ShortcutCoding.lean`) and
`close_pair_intermediate_card_le` (`CollisionReduction.lean`) with source-interval recovery. -/
theorem card_nearCollisions_slice_le
    {k r L m s_r j H U_y : ℕ} {R_r : ℝ} (hrL : r + L = k) (hRr : 0 ≤ R_r)
    {A : Finset ℕ}
    (hAsr : ∀ n ∈ A, oddCount r n = s_r)
    (hAj : ∀ n ∈ A, suffixOddCount r L n = j)
    (hUy : ∀ n ∈ A, T^[r] n ≤ U_y)
    (hOff : ∀ n ∈ A, (affineOffset r n : ℝ) / (3 : ℝ) ^ s_r ≤ R_r) :
    (nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
      (A.card : ℝ) *
        (∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)) *
        (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ)) * (R_r + 1) := by
  classical
  set NearSet := (A ×ˢ A).filter
    (fun p => T^[k] p.1 % 2 ^ m = T^[k] p.2 % 2 ^ m ∧ suffixHammingDist r L p.1 p.2 < H)
  -- For each fixed n ∈ A, bound the fiber {n' ∈ A : (n, n') ∈ NearSet}.
  have hfiber : ∀ n ∈ A,
      ((A.filter (fun n' => T^[k] n % 2 ^ m = T^[k] n' % 2 ^ m ∧
          suffixHammingDist r L n n' < H)).card : ℝ) ≤
        (∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)) *
        (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ)) * (R_r + 1) := by
    intro n hn
    set Fib := A.filter (fun n' => T^[k] n % 2 ^ m = T^[k] n' % 2 ^ m ∧
      suffixHammingDist r L n n' < H)
    set u : Fin L → Bool := parityWord L (T^[r] n)
    have hu_wt : wordWeight u = j := by
      unfold wordWeight; rw [← oddCount_eq_card_filter]; exact hAj n hn
    set Ball : Finset (Fin L → Bool) :=
      ((Finset.range (L + 1)).filter (fun i => 2 * i < H)).biUnion (fun i =>
        Finset.univ.filter (fun v : Fin L → Bool => wordWeight v = j ∧ wordHamming u v = 2 * i))
    have hBall_card : Ball.card ≤
        ∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          Nat.choose j i * Nat.choose (L - j) i := by
      calc Ball.card ≤ ∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
              (Finset.univ.filter (fun v : Fin L → Bool =>
                wordWeight v = j ∧ wordHamming u v = 2 * i)).card := Finset.card_biUnion_le
        _ = ∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
              Nat.choose j i * Nat.choose (L - j) i := by
            apply Finset.sum_congr rfl; intro i _
            rw [← hu_wt]; exact card_same_weight_hamming_sphere u i
    -- Partition Fib by v = parityWord L (T^[r] n') ∈ Ball.
    have hFib_cov : Fib ⊆ Ball.biUnion (fun v => Fib.filter (fun n' => parityWord L (T^[r] n') = v)) := by
      intro n' hn'
      have hn'F := Finset.mem_filter.mp hn'
      set v := parityWord L (T^[r] n')
      have hv_wt : wordWeight v = j := by
        unfold wordWeight; rw [← oddCount_eq_card_filter]; exact hAj n' hn'F.1
      have hwh : wordHamming u v = suffixHammingDist r L n n' := by
        unfold wordHamming suffixHammingDist
        exact (hammingDist_eq_card_filter L (T^[r] n) (T^[r] n')).symm
      have heven := wordHamming_same_weight_eq_two_mul u v (hu_wt.trans hv_wt.symm)
      set i := (Finset.univ.filter (fun l : Fin L => u l = true ∧ v l = false)).card
      have hi_le : i ≤ L := by
        calc i ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_filter_le _ _
          _ = L := Fintype.card_fin L
      have h2i_lt : 2 * i < H := by rw [← heven, hwh]; exact hn'F.2.2
      refine Finset.mem_biUnion.mpr ⟨v, ?_, Finset.mem_filter.mpr ⟨hn', rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), h2i_lt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_wt, heven⟩⟩
    -- For each fixed suffix word v ∈ Ball, bound #{n' ∈ Fib : parityWord L (T^[r] n') = v}.
    have hv_bound : ∀ v ∈ Ball,
        ((Fib.filter (fun n' => parityWord L (T^[r] n') = v)).card : ℝ) ≤
          ((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ) * (R_r + 1) := by
      intro v _
      set Fib_v := Fib.filter (fun n' => parityWord L (T^[r] n') = v)
      by_cases hemp : Fib_v.Nonempty
      · obtain ⟨n₀', hn0'⟩ := hemp
        have hn0'v := (Finset.mem_filter.mp hn0').2
        set B_v : ℕ := affineOffset L (T^[r] n₀')
        set Yset : Finset ℕ := (Finset.range (U_y + 1)).filter
          (fun y => (3 ^ j * y + B_v) % 2 ^ (L + m) = (2 ^ L * T^[k] n) % 2 ^ (L + m))
        have hY_card : Yset.card ≤ U_y / 2 ^ (L + m) + 1 :=
          close_pair_intermediate_card_le j B_v L m U_y (2 ^ L * T^[k] n)
        -- Every n' ∈ Fib_v has T^[r] n' ∈ Yset!
        have hFib_v_cov : Fib_v ⊆ Yset.biUnion (fun y => Fib_v.filter (fun n' => T^[r] n' = y)) := by
          intro n' hn'
          have hn'1 := Finset.mem_filter.mp hn'
          have hn'F := Finset.mem_filter.mp hn'1.1
          have hBv_eq : affineOffset L (T^[r] n') = B_v :=
            affineOffset_eq_of_parityWord_eq (hn'1.2.trans hn0'v.symm)
          have hiter : T^[L] (T^[r] n') = T^[k] n' := by
            rw [← Function.iterate_add_apply, Nat.add_comm L r, hrL]
          have haff := two_pow_mul_iterate L (T^[r] n')
          rw [hiter, hBv_eq] at haff
          have hodd_j : oddCount L (T^[r] n') = j := hAj n' hn'F.1
          rw [hodd_j] at haff
          have hmod_eq : (3 ^ j * T^[r] n' + B_v) % 2 ^ (L + m) =
              (2 ^ L * T^[k] n) % 2 ^ (L + m) := by
            rw [← haff, pow_add, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hn'F.2.1]
          refine Finset.mem_biUnion.mpr ⟨T^[r] n', ?_, Finset.mem_filter.mpr ⟨hn', rfl⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hUy n' hn'F.1)), hmod_eq⟩
        -- For each y ∈ Yset, #{n' ∈ Fib_v : T^[r] n' = y} ≤ R_r + 1.
        have hy_bound : ∀ y ∈ Yset, ((Fib_v.filter (fun n' => T^[r] n' = y)).card : ℝ) ≤ R_r + 1 := by
          intro y _
          set Fib_vy := Fib_v.filter (fun n' => T^[r] n' = y)
          by_cases hemp2 : Fib_vy.Nonempty
          · set lo : ℕ := Fib_vy.min' hemp2
            set hi : ℕ := Fib_vy.max' hemp2
            have hlo_mem : lo ∈ Fib_vy := Finset.min'_mem Fib_vy hemp2
            have hhi_mem : hi ∈ Fib_vy := Finset.max'_mem Fib_vy hemp2
            have hloA : lo ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hlo_mem).1).1).1
            have hhiA : hi ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hhi_mem).1).1).1
            have hlo_y : T^[r] lo = y := (Finset.mem_filter.mp hlo_mem).2
            have hhi_y : T^[r] hi = y := (Finset.mem_filter.mp hhi_mem).2
            have haff_lo : (2 : ℝ) ^ r * (y : ℝ) = (3 : ℝ) ^ s_r * (lo : ℝ) + (affineOffset r lo : ℝ) := by
              have := two_pow_mul_iterate r lo; rw [hlo_y, hAsr lo hloA] at this; exact_mod_cast this
            have haff_hi : (2 : ℝ) ^ r * (y : ℝ) = (3 : ℝ) ^ s_r * (hi : ℝ) + (affineOffset r hi : ℝ) := by
              have := two_pow_mul_iterate r hi; rw [hhi_y, hAsr hi hhiA] at this; exact_mod_cast this
            have hdiff_le : (hi : ℝ) - (lo : ℝ) ≤ R_r := by
              have h3pos : (0 : ℝ) < (3 : ℝ) ^ s_r := by positivity
              have heq : (hi : ℝ) - (lo : ℝ) =
                  (affineOffset r lo : ℝ) / (3 : ℝ) ^ s_r - (affineOffset r hi : ℝ) / (3 : ℝ) ^ s_r := by
                field_simp [h3pos.ne']; linarith
              have h0 : 0 ≤ (affineOffset r hi : ℝ) / (3 : ℝ) ^ s_r := by positivity
              linarith [heq, hOff lo hloA, h0]
            have hsub_Icc : Fib_vy ⊆ Finset.Icc lo hi := by
              intro z hz
              exact Finset.mem_Icc.mpr ⟨Finset.min'_le Fib_vy z hz, Finset.le_max' Fib_vy z hz⟩
            have hcard_le : Fib_vy.card ≤ hi - lo + 1 := by
              calc Fib_vy.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsub_Icc
                _ = hi + 1 - lo := Nat.card_Icc lo hi
                _ = hi - lo + 1 := by
                    have hle : lo ≤ hi := Finset.min'_le Fib_vy hi hhi_mem
                    omega
            have hcast_le : (Fib_vy.card : ℝ) ≤ (hi : ℝ) - (lo : ℝ) + 1 := by
              have hle : lo ≤ hi := Finset.min'_le Fib_vy hi hhi_mem
              have : ((hi - lo + 1 : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) + 1 := by
                rw [Nat.cast_add, Nat.cast_sub hle]; norm_num
              rw [← this]; exact_mod_cast hcard_le
            linarith
          · rw [Finset.not_nonempty_iff_eq_empty.mp hemp2, Finset.card_empty, Nat.cast_zero]
            linarith
        have hnat : Fib_v.card ≤ ∑ y ∈ Yset, (Fib_v.filter (fun n' => T^[r] n' = y)).card :=
          (Finset.card_le_card hFib_v_cov).trans Finset.card_biUnion_le
        calc (Fib_v.card : ℝ)
            ≤ ∑ y ∈ Yset, ((Fib_v.filter (fun n' => T^[r] n' = y)).card : ℝ) := by exact_mod_cast hnat
          _ ≤ ∑ _y ∈ Yset, (R_r + 1) := Finset.sum_le_sum hy_bound
          _ = (Yset.card : ℝ) * (R_r + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ) * (R_r + 1) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hY_card) (by linarith)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
        positivity
    have hFib_nat : Fib.card ≤ ∑ v ∈ Ball, (Fib.filter (fun n' => parityWord L (T^[r] n') = v)).card :=
      (Finset.card_le_card hFib_cov).trans Finset.card_biUnion_le
    calc (Fib.card : ℝ)
        ≤ ∑ v ∈ Ball, ((Fib.filter (fun n' => parityWord L (T^[r] n') = v)).card : ℝ) := by
          exact_mod_cast hFib_nat
      _ ≤ ∑ _v ∈ Ball, (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ) * (R_r + 1)) := Finset.sum_le_sum hv_bound
      _ = (Ball.card : ℝ) * (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ) * (R_r + 1)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
            ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)) *
          (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ)) * (R_r + 1) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hBall_card
  have hNear_sum : NearSet.card =
      ∑ n ∈ A, (A.filter (fun n' => T^[k] n % 2 ^ m = T^[k] n' % 2 ^ m ∧
        suffixHammingDist r L n n' < H)).card := by
    have hpart : NearSet = A.biUnion (fun n =>
        (A.filter (fun n' => T^[k] n % 2 ^ m = T^[k] n' % 2 ^ m ∧
          suffixHammingDist r L n n' < H)).image (fun n' => (n, n'))) := by
      ext ⟨n, n'⟩
      simp only [NearSet, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro ⟨⟨hn, hn'⟩, h1, h2⟩; exact ⟨n, hn, n', ⟨hn', h1, h2⟩, rfl, rfl⟩
      · rintro ⟨n₀, hn₀, n₀', ⟨hn₀', h1, h2⟩, rfl, rfl⟩; exact ⟨⟨hn₀, hn₀'⟩, h1, h2⟩
    rw [hpart, Finset.card_biUnion]
    · apply Finset.sum_congr rfl; intro n _
      exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    · intro n₁ _ n₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
      rintro ⟨x, y⟩ ⟨_, _, h1⟩ ⟨_, _, h2⟩
      exact hne ((Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm)
  change (NearSet.card : ℝ) ≤ _
  rw [hNear_sum, Nat.cast_sum]
  calc
    ∑ n ∈ A, ((A.filter (fun n' => T^[k] n % 2 ^ m = T^[k] n' % 2 ^ m ∧
        suffixHammingDist r L n n' < H)).card : ℝ)
      ≤ ∑ _n ∈ A,
          ((∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
            ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)) *
          (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ)) * (R_r + 1)) := Finset.sum_le_sum hfiber
    _ = (A.card : ℝ) *
        (∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)) *
        (((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ)) * (R_r + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-! ## 2. Unconditional All-Shell, High-Product Tail, & Good-Shell Slice-to-Shell Assembly -/

/-- Exact two-window product-prefix survivor set `S_k` on dyadic shell `[2^k, 2^(k+1))`
matching Theorem 1 of Paper 1 (`e = 10^{-7}`, `m = ⌊0.508 k⌋ = (508 * k) / 1000`). -/
noncomputable def twoWindowSurvivors (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n =>
    ∀ i : ℕ, i ≤ k + (508 * k) / 1000 →
      (2 : ℝ) ^ ((1 - (1 : ℝ) / 10 ^ 7) * (i : ℝ)) ≤ (3 : ℝ) ^ oddCount i n)

/-- Every never-dropping start on shell `k ≥ 24` belongs to `twoWindowSurvivors k`. -/
theorem shellNeverDrops_le_twoWindowSurvivors {k : ℕ} (hk : 24 ≤ k) :
    shellNeverDrops k ≤ (twoWindowSurvivors k).card := by
  classical
  unfold shellNeverDrops twoWindowSurvivors
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  have hn_ge24 : 2 ^ 24 ≤ n :=
    le_trans (Nat.pow_le_pow_right (by decide) hk) (Finset.mem_Ico.mp hn.1).1
  have hn_pos : 0 < n := lt_of_lt_of_le (by positivity) hn_ge24
  have hstep := step_correction_le_two_pow_1e7 hn_ge24
  have hnodrop : ∀ j : ℕ, j ≤ k + (508 * k) / 1000 → n ≤ T^[j] n := by
    intro j _
    cases j with
    | zero => simp
    | succ j' => exact hn.2 (j' + 1) (by omega)
  exact prefix_product_lower_of_no_drop hn_pos hstep hnodrop

/-- Helper: `2^c ≤ 3^s` implies `(Real.log 2 / Real.log 3) * c ≤ s`. -/
private lemma oddCount_ge_of_rpow_le_three_pow {c : ℝ} {s : ℕ}
    (h : (2 : ℝ) ^ c ≤ (3 : ℝ) ^ s) :
    (Real.log 2 / Real.log 3) * c ≤ (s : ℝ) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log ((2 : ℝ) ^ c) ≤ Real.log ((3 : ℝ) ^ s) :=
    Real.log_le_log (by positivity) h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_pow] at hlog
  rw [div_mul_eq_mul_div, div_le_iff₀ hlog3]
  linarith

/-- Helper: `3^s < 2^c` implies `s < (Real.log 2 / Real.log 3) * c`. -/
private lemma oddCount_lt_of_three_pow_lt_rpow {c : ℝ} {s : ℕ}
    (h : (3 : ℝ) ^ s < (2 : ℝ) ^ c) :
    (s : ℝ) < (Real.log 2 / Real.log 3) * c := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log ((3 : ℝ) ^ s) < Real.log ((2 : ℝ) ^ c) :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_pow] at hlog
  rw [div_mul_eq_mul_div, lt_div_iff₀ hlog3]
  linarith

/-- Helper: bijection `n ↦ n - 2^k` maps any `S ⊆ Ico (2^k) (2^(k+1))` into `range (2^k)`
preserving `oddCount k`. -/
private lemma card_shell_filter_ge_le {k : ℕ} {s₀ z : ℝ}
    (hz_half : (1 : ℝ) / 2 ≤ z) (hz1 : z < 1) :
    (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => s₀ ≤ (oddCount k n : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ crossEntropy (k : ℝ) s₀ z := by
  set S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => s₀ ≤ (oddCount k n : ℝ))
  set T := (Finset.range (2 ^ k)).filter (fun y => s₀ ≤ (oddCount k y : ℝ))
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun n _ => n - 2 ^ k)
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hI := Finset.mem_Ico.mp hn'.1
      have h2p : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hodd : oddCount k (n - 2 ^ k) = oddCount k n := by
        have h := oddCount_add_two_pow_mul k (n - 2 ^ k) 1
        rw [show n - 2 ^ k + 1 * 2 ^ k = n by omega] at h
        exact h.symm
      rw [hodd]; exact hn'.2
    · intro n₁ hn₁ n₂ hn₂ heq
      have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1).1
      have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1).1
      omega
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hylt := Finset.mem_range.mp hy'.1
      have h2p : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      refine ⟨y + 2 ^ k, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hodd : oddCount k (y + 2 ^ k) = oddCount k y := by
        simpa using oddCount_add_two_pow_mul k y 1
      rw [hodd]; exact hy'.2
  rw [hcard]
  exact card_residue_menu_le hz_half hz1

/-- **Unconditional All-Shell Lagarias One-Window Bound (`S_k ≤ 2^{0.94995558 k}`):**
Holds for EVERY `k : ℕ` with multiplicative constant `1`. -/
theorem all_shell_twoWindowSurvivors_le (k : ℕ) :
    ((twoWindowSurvivors k).card : ℝ) ≤ (2 : ℝ) ^ ((94995558 / 10 ^ 8 : ℝ) * (k : ℝ)) := by
  classical
  set p := Real.log 2 / Real.log 3
  set s₀ : ℝ := (1 - (1 : ℝ) / 10 ^ 7) * p * (k : ℝ)
  have hsub : twoWindowSurvivors k ⊆
      (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => s₀ ≤ (oddCount k n : ℝ)) := by
    intro n hn
    rw [twoWindowSurvivors, Finset.mem_filter] at hn
    rw [Finset.mem_filter]
    refine ⟨hn.1, ?_⟩
    have hpow := hn.2 k (Nat.le_add_right k _)
    have hge := oddCount_ge_of_rpow_le_three_pow hpow
    dsimp [s₀, p]; linarith
  have h1 : ((twoWindowSurvivors k).card : ℝ) ≤ (2 : ℝ) ^ crossEntropy (k : ℝ) s₀ (63093 / 10 ^ 5) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub)
      (card_shell_filter_ge_le (by norm_num) (by norm_num))
  have hce : crossEntropy (k : ℝ) s₀ (63093 / 10 ^ 5) =
      crossEntropy 1 ((1 - (1 : ℝ) / 10 ^ 7) * p) (63093 / 10 ^ 5) * (k : ℝ) := by
    unfold crossEntropy; dsimp [s₀]; ring
  rw [hce] at h1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right all_shell_lagarias_tilt_bound.le (Nat.cast_nonneg k)))

/-- **Unconditional All-Shell Never-Drops Bound (`N_k ≤ 2^{0.94995558 k}` for all `k ≥ 24`):**
Directly discharges the `hall` field of `ShellSeparationCovering` with zero hypotheses. -/
theorem all_shell_neverDrops_le {k : ℕ} (hk : 24 ≤ k) :
    (shellNeverDrops k : ℝ) ≤ (2 : ℝ) ^ ((94995558 / 10 ^ 8 : ℝ) * (k : ℝ)) :=
  le_trans (by exact_mod_cast shellNeverDrops_le_twoWindowSurvivors hk)
    (all_shell_twoWindowSurvivors_le k)

/-- **Unconditional High-Product Tail Bound (`δ ≥ 0.012`):**
At most `2^{0.943928 k}` starts in `twoWindowSurvivors k` have `3^{s_k(n)} ≥ 2^{1.012 k}`. -/
theorem high_product_tail_card_le (k : ℕ) :
    (((twoWindowSurvivors k).filter
      (fun n => (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ oddCount k n)).card : ℝ) ≤
      (2 : ℝ) ^ ((943928 / 10 ^ 6 : ℝ) * (k : ℝ)) := by
  classical
  set p := Real.log 2 / Real.log 3
  set s₀ : ℝ := (1012 / 1000 : ℝ) * p * (k : ℝ)
  have hsub :
      (twoWindowSurvivors k).filter
        (fun n => (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ oddCount k n) ⊆
      (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter (fun n => s₀ ≤ (oddCount k n : ℝ)) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨(Finset.mem_filter.mp hn.1).1, ?_⟩
    have hge := oddCount_ge_of_rpow_le_three_pow hn.2
    dsimp [s₀, p]; linarith
  have h1 : (((twoWindowSurvivors k).filter
      (fun n => (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ oddCount k n)).card : ℝ) ≤
      (2 : ℝ) ^ crossEntropy (k : ℝ) s₀ (64 / 100) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub)
      (card_shell_filter_ge_le (by norm_num) (by norm_num))
  have hce : crossEntropy (k : ℝ) s₀ (64 / 100) =
      crossEntropy 1 ((1012 / 1000 : ℝ) * p) (64 / 100) * (k : ℝ) := by
    unfold crossEntropy; dsimp [s₀]; ring
  rw [hce] at h1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right high_product_tail_bound.le (Nat.cast_nonneg k)))

/-- Prefix-residue shift injectivity on shell `k` at separation slack `σ`
(Paper 1 Section 3.4 Step 2 & Section 3.5 Step 1). -/
def HasWrapSeparation (σ : ℝ) (k : ℕ) : Prop :=
  let m : ℕ := (508 * k) / 1000
  let p : ℝ := Real.log 2 / Real.log 3
  ∀ s : ℕ, s ≤ k →
    (2 : ℝ) ^ ((1 - (1 : ℝ) / 10 ^ 7) * (k : ℝ)) ≤ (3 : ℝ) ^ s →
    (3 : ℝ) ^ s < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) →
    let δ : ℝ := (s : ℝ) / (p * (k : ℝ)) - 1
    let r : ℕ := Nat.ceil ((492 / 1000 + δ + 3 / 10 ^ 7 + σ) * (k : ℝ))
    ∀ n₁ ∈ twoWindowSurvivors k, ∀ n₁' ∈ twoWindowSurvivors k,
    ∀ n₂ ∈ twoWindowSurvivors k, ∀ n₂' ∈ twoWindowSurvivors k,
      oddCount k n₁ = s → oddCount k n₁' = s →
      oddCount k n₂ = s → oddCount k n₂' = s →
      T^[k] n₁ % 2 ^ m = T^[k] n₁' % 2 ^ m →
      T^[k] n₂ % 2 ^ m = T^[k] n₂' % 2 ^ m →
      n₁ % 2 ^ r = n₂ % 2 ^ r →
      n₁' % 2 ^ r = n₂' % 2 ^ r →
      (n₁' : ℤ) - (n₁ : ℤ) = (n₂' : ℤ) - (n₂ : ℤ)

/-- Helper: `k ≤ 2 ^ (c * k)` for `k ≥ 2 ^ 40` and `c ≥ 10^{-8}` (from `prefactor_absorption_ge_two_pow_40`). -/
private lemma nat_le_two_rpow_small {k : ℕ} (hk : 2 ^ 40 ≤ k) :
    (k : ℝ) ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) := by
  have hpa := prefactor_absorption_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le (by positivity) hk; exact_mod_cast this
  have hlog : Real.logb 2 (k : ℝ) < (4 / 10 ^ 9 : ℝ) * (k : ℝ) := by
    have h1 : Real.logb 2 (k : ℝ) ≤ Real.logb 2 ((k : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hk_pos (by linarith)
    have h2 : 0 ≤ Real.logb 2 ((k : ℝ) + 1) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hk_pos]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog.le

/-- Helper: from `Int` mod equality to divisibility of difference. -/
private lemma int_dvd_sub_of_emod_eq {a b m : ℤ} (h : a % m = b % m) : m ∣ a - b :=
  Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, h, sub_self, Int.zero_emod])

/-- Helper: `2 ^ 40 ≤ k` implies `(1099511627776 : ℝ) ≤ (k : ℝ)`. -/
private lemma cast_ge_two_pow_40 {k : ℕ} (hk : 2 ^ 40 ≤ k) :
    (1099511627776 : ℝ) ≤ (k : ℝ) := by
  have h1 : (1099511627776 : ℕ) ≤ k := le_trans (by norm_num) hk
  exact_mod_cast h1

/-- Helper part 1 for `wrap_separation_failure_witness`: slope ratio, `|Z| ≤ 2 |X|`, and
Euclidean norm bound `X^2 + Z^2 ≤ (2^(1.50801 * k))^2`. -/
private lemma wrap_failure_slope_and_norm {σ δ ρ R : ℝ} {k m r s : ℕ} {t a : ℤ}
    (hk : 2 ^ 40 ≤ k) (hrle : r ≤ k + m)
    (hσ_lo : (1 : ℝ) / 10 ^ 7 ≤ σ)
    (hρ : ρ = 492 / 1000 + δ + 3 / 10 ^ 7 + σ)
    (hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ))
    (hr_ge : ρ * (k : ℝ) ≤ (r : ℝ))
    (hR_eq : R = ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)))
    (h3s_eq : (3 : ℝ) ^ s = (2 : ℝ) ^ ((1 + δ) * (k : ℝ)))
    (h3hi : (3 : ℝ) ^ s < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)))
    (ht_ne : t ≠ 0)
    (hX_ne : t * (2 : ℤ) ^ (k + m - r) ≠ 0)
    (hZX_bound : |((a * (3 : ℤ) ^ s : ℤ) : ℝ) - ((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ)| ≤
      2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r)
    (ht_bound : |(t : ℝ)| ≤ 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m) :
    let X : ℤ := t * (2 : ℤ) ^ (k + m - r)
    let Z : ℤ := a * (3 : ℤ) ^ s
    |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-(49597 / 100000 : ℝ) * (k : ℝ)) ∧
    |(Z : ℝ)| ≤ 2 * |(X : ℝ)| ∧
    (X : ℝ) ^ 2 + (Z : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2 := by
  intro X Z
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hR_nonneg : 0 ≤ R := by rw [hR_eq]; positivity
  have hX_ge_M : (2 : ℝ) ^ (k + m - r) ≤ |(X : ℝ)| := by
    have hXcast : (X : ℝ) = (t : ℝ) * (2 : ℝ) ^ (k + m - r) := by dsimp [X]; push_cast; rfl
    rw [hXcast, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + m - r))]
    have ht1 : (1 : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast Int.one_le_abs ht_ne
    simpa using mul_le_mul_of_nonneg_right ht1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + m - r))
  have hZX_ratio : |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-(49597 / 100000 : ℝ) * (k : ℝ)) := by
    have hXr_ne : (X : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hX_ne
    have hsub : (Z : ℝ) / (X : ℝ) - 1 = ((Z : ℝ) - (X : ℝ)) / (X : ℝ) := by field_simp [hXr_ne]
    rw [hsub, abs_div]
    have hstep1 : |(Z : ℝ) - (X : ℝ)| / |(X : ℝ)| ≤
        (2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) / (2 : ℝ) ^ (k + m - r) :=
      div_le_div₀ (by positivity) hZX_bound (by positivity) hX_ge_M
    have hcomb : (2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r) / (2 : ℝ) ^ (k + m - r) =
        2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ (k + m) := by
      rw [div_div, ← pow_add, Nat.add_sub_of_le hrle]
    rw [hcomb] at hstep1
    have h2km_ge : (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ) - 1) ≤ (2 : ℝ) ^ (k + m) := by
      rw [← Real.rpow_natCast (2 : ℝ) (k + m)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast; linarith
    have hk_pow := nat_le_two_rpow_small hk
    have h2R : 2 * R ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
      calc 2 * R = (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by rw [hR_eq]; ring
        _ ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hk_pow (by positivity)
        _ = (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have hnum_le : 2 * R * (3 : ℝ) ^ s ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 + 1012 / 1000 : ℝ) * (k : ℝ)) := by
      calc 2 * R * (3 : ℝ) ^ s
          ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) :=
            mul_le_mul h2R h3hi.le (by positivity) (by positivity)
        _ = (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 + 1012 / 1000 : ℝ) * (k : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have hdiv_le : 2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ (k + m) ≤
        (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 + 1012 / 1000 : ℝ) * (k : ℝ)) /
          (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ) - 1) :=
      div_le_div₀ (by positivity) hnum_le (by positivity) h2km_ge
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv_le
    exact (hstep1.trans hdiv_le).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hZ_le_2X : |(Z : ℝ)| ≤ 2 * |(X : ℝ)| := by
    have hhalf : |(Z : ℝ) / (X : ℝ) - 1| ≤ 1 :=
      hZX_ratio.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
    have hXr_ne : (X : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hX_ne
    have h1 : |(Z : ℝ) - (X : ℝ)| / |(X : ℝ)| ≤ 1 := by
      have : (Z : ℝ) / (X : ℝ) - 1 = ((Z : ℝ) - (X : ℝ)) / (X : ℝ) := by field_simp [hXr_ne]
      rwa [this, abs_div] at hhalf
    have h2 : |(Z : ℝ) - (X : ℝ)| ≤ |(X : ℝ)| := (div_le_one (abs_pos.mpr hXr_ne)).mp h1
    have htri : |(Z : ℝ)| - |(X : ℝ)| ≤ |(Z : ℝ) - (X : ℝ)| := abs_sub_abs_le_abs_sub _ _
    linarith
  have hX_upper : |(X : ℝ)| ≤ 6 * (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ)) := by
    have hXcast : (X : ℝ) = (t : ℝ) * (2 : ℝ) ^ (k + m - r) := by dsimp [X]; push_cast; rfl
    rw [hXcast, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + m - r))]
    have h1 : |(t : ℝ)| * (2 : ℝ) ^ (k + m - r) ≤
        (6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m) * (2 : ℝ) ^ (k + m - r) :=
      mul_le_mul_of_nonneg_right ht_bound (by positivity)
    have h2 : (6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m) * (2 : ℝ) ^ (k + m - r) =
        6 * (3 : ℝ) ^ s * (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
      have hpow : (2 : ℝ) ^ (k + m - r) * (2 : ℝ) ^ r = (2 : ℝ) ^ k * (2 : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hrle, pow_add]
      field_simp [(by positivity : (0 : ℝ) < (2 : ℝ) ^ m).ne', (by positivity : (0 : ℝ) < (2 : ℝ) ^ r).ne']
      linarith [show 6 * (3 : ℝ) ^ s * ((2 : ℝ) ^ (k + m - r) * (2 : ℝ) ^ r) =
          6 * (3 : ℝ) ^ s * ((2 : ℝ) ^ k * (2 : ℝ) ^ m) by rw [hpow]]
    rw [h2, h3s_eq] at h1
    have hpow_le : (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) * (2 : ℝ) ^ k / (2 : ℝ) ^ r ≤
        (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast (2 : ℝ) r,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hρ] at hr_ge; nlinarith
    have hmul := mul_le_mul_of_nonneg_left hpow_le (by norm_num : (0 : ℝ) ≤ 6)
    have h1' : |(t : ℝ)| * (2 : ℝ) ^ (k + m - r) ≤
        6 * ((2 : ℝ) ^ ((1 + δ) * (k : ℝ)) * (2 : ℝ) ^ k / (2 : ℝ) ^ r) := by
      have heq : 6 * (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) * (2 : ℝ) ^ k / (2 : ℝ) ^ r =
          6 * ((2 : ℝ) ^ ((1 + δ) * (k : ℝ)) * (2 : ℝ) ^ k / (2 : ℝ) ^ r) := by ring
      rwa [heq] at h1
    exact h1'.trans hmul
  have hnorm_sq : (X : ℝ) ^ 2 + (Z : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2 := by
    have hZsq : (Z : ℝ) ^ 2 ≤ 4 * (X : ℝ) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (Z : ℝ)) hZ_le_2X
      nlinarith [sq_abs (Z : ℝ), sq_abs (X : ℝ)]
    have h18 : (18 : ℝ) * (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ)) ≤
        (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) := by
      have h25 : (18 : ℝ) ≤ (2 : ℝ) ^ ((1 / 100000 : ℝ) * (k : ℝ)) :=
        (by norm_num : (18 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ)).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
      calc (18 : ℝ) * (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ))
          ≤ (2 : ℝ) ^ ((1 / 100000 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1508 / 1000 : ℝ) * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right h25 (by positivity)
        _ = (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have h3X : 3 * |(X : ℝ)| ≤ (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) := by
      linarith [hX_upper, h18]
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 3 * |(X : ℝ)|) h3X
    nlinarith [sq_abs (X : ℝ), hZsq, hsq]
  exact ⟨hZX_ratio, hZ_le_2X, hnorm_sq⟩

/-- Helper part 2a: sharp upper bound on `24 * R * 3^s / 2^(m + r)` below `2^(-1.50801 * (σ/2) * k)`. -/
private lemma wrap_failure_lhs_lt {σ δ ρ R : ℝ} {k m r s : ℕ}
    (hσ_lo : (1 : ℝ) / 10 ^ 7 ≤ σ)
    (hk : 2 ^ 40 ≤ k)
    (hρ : ρ = 492 / 1000 + δ + 3 / 10 ^ 7 + σ)
    (hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ))
    (hr_ge : ρ * (k : ℝ) ≤ (r : ℝ))
    (hR_eq : R = ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)))
    (h3s_eq : (3 : ℝ) ^ s = (2 : ℝ) ^ ((1 + δ) * (k : ℝ))) :
    24 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ (m + r) <
      (2 : ℝ) ^ (-(150801 / 100000 : ℝ) * (σ / 2) * (k : ℝ)) := by
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  rw [h3s_eq]
  have h2mr_ge : (2 : ℝ) ^ (((1 + δ + 3 / 10 ^ 7 + σ) * (k : ℝ)) - 1) ≤ (2 : ℝ) ^ (m + r) := by
    rw [← Real.rpow_natCast (2 : ℝ) (m + r)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; rw [hρ] at hr_ge; linarith
  have hk_pow := nat_le_two_rpow_small hk
  have hnum_le : 24 * R * (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) ≤
      (2 : ℝ) ^ (4 + (4 / 10 ^ 9 + 1 / 10 ^ 7 + (1 + δ)) * (k : ℝ)) := by
    have h24R : 24 * R = 12 * (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by rw [hR_eq]; ring
    rw [h24R]
    have h12k : 12 * (k : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ) * (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) :=
      mul_le_mul (by norm_num : (12 : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ)) hk_pow (by positivity) (by positivity)
    calc 12 * (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 + δ) * (k : ℝ))
        ≤ (2 : ℝ) ^ (4 : ℝ) * (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) *
            (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h12k (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ (4 + (4 / 10 ^ 9 + 1 / 10 ^ 7 + (1 + δ)) * (k : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  have hdiv_le : 24 * R * (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) / (2 : ℝ) ^ (m + r) ≤
      (2 : ℝ) ^ (4 + (4 / 10 ^ 9 + 1 / 10 ^ 7 + (1 + δ)) * (k : ℝ)) /
        (2 : ℝ) ^ (((1 + δ + 3 / 10 ^ 7 + σ) * (k : ℝ)) - 1) :=
    div_le_div₀ (by positivity) hnum_le (by positivity) h2mr_ge
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv_le
  refine lt_of_le_of_lt hdiv_le (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_)
  have hσk : (1 / 10 ^ 7 : ℝ) * (k : ℝ) ≤ σ * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hσ_lo hk_pos.le
  linarith [hk_r, hσk]

/-- Helper part 2 for `wrap_separation_failure_witness`: primitive height and three-place
product upper bound `< (x^2 + z^2)^(-(σ/2)/2)`. -/
private lemma wrap_failure_primitive_bounds {σ H₀ δ ρ R : ℝ} {k m r s : ℕ} {t a : ℤ}
    (hσ_lo : (1 : ℝ) / 10 ^ 7 ≤ σ)
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hk : 2 ^ 40 ≤ k) (hrle : r ≤ k + m)
    (hρ : ρ = 492 / 1000 + δ + 3 / 10 ^ 7 + σ)
    (hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ))
    (hr_ge : ρ * (k : ℝ) ≤ (r : ℝ))
    (hR_eq : R = ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)))
    (h3s_eq : (3 : ℝ) ^ s = (2 : ℝ) ^ ((1 + δ) * (k : ℝ)))
    (h3hi : (3 : ℝ) ^ s < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)))
    (ht_ne : t ≠ 0) (ha_ne : a ≠ 0)
    (hX_ne : t * (2 : ℤ) ^ (k + m - r) ≠ 0)
    (hXZ_ne : t * (2 : ℤ) ^ (k + m - r) ≠ a * (3 : ℤ) ^ s)
    (hZX_bound : |((a * (3 : ℤ) ^ s : ℤ) : ℝ) - ((t * (2 : ℤ) ^ (k + m - r) : ℤ) : ℝ)| ≤
      2 * R * (3 : ℝ) ^ s / (2 : ℝ) ^ r)
    (ht_bound : |(t : ℝ)| ≤ 6 * (3 : ℝ) ^ s / (2 : ℝ) ^ m) :
    let X : ℤ := t * (2 : ℤ) ^ (k + m - r)
    let Z : ℤ := a * (3 : ℤ) ^ s
    H₀ ≤ max |(X / (Int.gcd X Z : ℤ) : ℝ)| |(Z / (Int.gcd X Z : ℤ) : ℝ)| ∧
    threePlaceProduct X Z <
      (((X / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2 +
        ((Z / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2) ^ (-(σ / 2) / 2) ∧
    |(X : ℝ)| ≤ (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) ∧
    |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-(49597 / 100000 : ℝ) * (k : ℝ)) := by
  intro X Z
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hR_nonneg : 0 ≤ R := by rw [hR_eq]; positivity
  obtain ⟨hZX_ratio, hZ_le_2X, hnorm_sq⟩ :=
    wrap_failure_slope_and_norm hk hrle hσ_lo hρ hm_ge hr_ge hR_eq h3s_eq h3hi
      ht_ne hX_ne hZX_bound ht_bound
  have hX_hi : |(X : ℝ)| ≤ (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) := by
    have hsq : |(X : ℝ)| ^ 2 ≤ ((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2 := by
      rw [sq_abs]; nlinarith [sq_nonneg (Z : ℝ), hnorm_sq]
    nlinarith [abs_nonneg (X : ℝ), show (0 : ℝ) ≤ (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) by positivity]
  set g : ℕ := Int.gcd X Z
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left Z.natAbs (Int.natAbs_pos.mpr hX_ne)
  have hg_r : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_pos
  have hXg : (g : ℤ) * (X / (g : ℤ)) = X := Int.mul_ediv_cancel' (Int.gcd_dvd_left X Z)
  have hZg : (g : ℤ) * (Z / (g : ℤ)) = Z := Int.mul_ediv_cancel' (Int.gcd_dvd_right X Z)
  have hx_cast : ((X / (g : ℤ) : ℤ) : ℝ) = (X : ℝ) / (g : ℝ) := by
    have h1 : (g : ℝ) * ((X / (g : ℤ) : ℤ) : ℝ) = (X : ℝ) := by exact_mod_cast hXg
    field_simp [(by linarith : (g : ℝ) ≠ 0)]; linarith
  have hz_cast : ((Z / (g : ℤ) : ℤ) : ℝ) = (Z : ℝ) / (g : ℝ) := by
    have h1 : (g : ℝ) * ((Z / (g : ℤ) : ℤ) : ℝ) = (Z : ℝ) := by exact_mod_cast hZg
    field_simp [(by linarith : (g : ℝ) ≠ 0)]; linarith
  have hx_ge : (2 : ℝ) ^ ((49597 / 100000 : ℝ) * (k : ℝ)) ≤ |(X / (g : ℤ) : ℝ)| := by
    have hx_ne : X / (g : ℤ) ≠ 0 := by intro h0; rw [h0, mul_zero] at hXg; exact hX_ne hXg.symm
    have hxz_ne : Z / (g : ℤ) - X / (g : ℤ) ≠ 0 := by
      intro h0
      have hXZ' : X = Z := by
        have : Z / (g : ℤ) = X / (g : ℤ) := sub_eq_zero.mp h0
        rw [← hXg, ← hZg, this]
      exact hXZ_ne hXZ'
    have h1 : (1 : ℝ) / |(X : ℝ) / (g : ℝ)| ≤ |(Z : ℝ) / (X : ℝ) - 1| := by
      have heq : (Z : ℝ) / (X : ℝ) - 1 = (((Z / (g : ℤ) - X / (g : ℤ) : ℤ) : ℝ)) / ((X / (g : ℤ) : ℤ) : ℝ) := by
        have hXr : (X : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hX_ne
        have hgr : (g : ℝ) ≠ 0 := by linarith
        push_cast; rw [hx_cast, hz_cast]; field_simp [hXr, hgr]
      conv_rhs => rw [heq, abs_div, hx_cast]
      have hge1 : (1 : ℝ) ≤ |((Z / (g : ℤ) - X / (g : ℤ) : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hxz_ne
      exact div_le_div_of_nonneg_right hge1 (abs_nonneg ((X : ℝ) / (g : ℝ)))
    have h2 := h1.trans hZX_ratio
    rw [neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div] at h2
    have hx_pos : 0 < |(X : ℝ) / (g : ℝ)| := by
      rw [← hx_cast]; exact abs_pos.mpr (Int.cast_ne_zero.mpr hx_ne)
    simpa [Int.cast_natCast] using (inv_le_inv₀ hx_pos (by positivity)).mp h2
  have hH_ok : H₀ ≤ max |(X / (g : ℤ) : ℝ)| |(Z / (g : ℤ) : ℝ)| := by
    have hk_r' : ((2 ^ 40 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk_mono : (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ ((49597 / 100000 : ℝ) * (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hk_r' (by norm_num))
    exact (hH₀.trans (hk_mono.trans hx_ge)).trans (le_max_left _ _)
  have htp_le := wrap_separation_three_place_bound ht_ne ha_ne hR_nonneg hZX_bound ht_bound hZ_le_2X
  have hxz_sq_le : ((X / (g : ℤ) : ℤ) : ℝ) ^ 2 + ((Z / (g : ℤ) : ℤ) : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2 := by
    rw [hx_cast, hz_cast]
    have h1 : ((X : ℝ) / (g : ℝ)) ^ 2 + ((Z : ℝ) / (g : ℝ)) ^ 2 = ((X : ℝ) ^ 2 + (Z : ℝ) ^ 2) / (g : ℝ) ^ 2 := by ring
    rw [h1]
    exact (div_le_self (by positivity) (by nlinarith : (1 : ℝ) ≤ (g : ℝ) ^ 2)).trans hnorm_sq
  have hxz_pos : (0 : ℝ) < ((X / (g : ℤ) : ℤ) : ℝ) ^ 2 + ((Z / (g : ℤ) : ℤ) : ℝ) ^ 2 := by
    have hx_ne : X / (g : ℤ) ≠ 0 := by intro h0; rw [h0, mul_zero] at hXg; exact hX_ne hXg.symm
    have h1 : (0 : ℝ) < ((X / (g : ℤ) : ℤ) : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hx_ne)
    nlinarith [sq_nonneg ((Z / (g : ℤ) : ℤ) : ℝ)]
  have hrhs_ge : (2 : ℝ) ^ (-(150801 / 100000 : ℝ) * (σ / 2) * (k : ℝ)) ≤
      (((X / (g : ℤ) : ℤ) : ℝ) ^ 2 + ((Z / (g : ℤ) : ℤ) : ℝ) ^ 2) ^ (-(σ / 2) / 2) := by
    have h1 : (((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2) ^ (-(σ / 2) / 2) ≤
        (((X / (g : ℤ) : ℤ) : ℝ) ^ 2 + ((Z / (g : ℤ) : ℤ) : ℝ) ^ 2) ^ (-(σ / 2) / 2) :=
      Real.rpow_le_rpow_of_nonpos hxz_pos hxz_sq_le (by linarith)
    have h2 : (((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) ^ 2) ^ (-(σ / 2) / 2) =
        (2 : ℝ) ^ (-(150801 / 100000 : ℝ) * (σ / 2) * (k : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rwa [h2] at h1
  have hlhs_lt := wrap_failure_lhs_lt hσ_lo hk hρ hm_ge hr_ge hR_eq h3s_eq
  exact ⟨hH_ok, (htp_le.trans_lt hlhs_lt).trans_le hrhs_ge, hX_hi, hZX_ratio⟩

/-- **Wrap-Separation Failure Produces an Exact 3-Place Subspace Witness:**
If `HasWrapSeparation σ k` fails at any shell `k ≥ 2^{40}` (for `σ ∈ {10^{-4}, 10^{-7}}`),
then there exists a nonzero non-diagonal integer vector `(X, Z)` satisfying ALL hypotheses
of `subspace_implies_exceptional_bands` (`CollisionReduction.lean`) with
`δ_ST = σ / 2`, `c_lo = 0.49597`, `c_hi = 1.50801`, and `H₀ ≤ 2^(0.49597 * 2^40)`. -/
theorem wrap_separation_failure_witness {σ H₀ : ℝ} {k : ℕ}
    (hσ : σ = 1 / 10 ^ 4 ∨ σ = 1 / 10 ^ 7)
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hk : 2 ^ 40 ≤ k)
    (hfail : ¬ HasWrapSeparation σ k) :
    ∃ X Z : ℤ, X ≠ 0 ∧ Z ≠ 0 ∧ X ≠ Z ∧
      H₀ ≤ max |(X / (Int.gcd X Z : ℤ) : ℝ)| |(Z / (Int.gcd X Z : ℤ) : ℝ)| ∧
      threePlaceProduct X Z <
        (((X / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2 +
          ((Z / (Int.gcd X Z : ℤ) : ℤ) : ℝ) ^ 2) ^ (-(σ / 2) / 2) ∧
      |(X : ℝ)| ≤ (2 : ℝ) ^ ((150801 / 100000 : ℝ) * (k : ℝ)) ∧
      |(Z : ℝ) / (X : ℝ) - 1| ≤ (2 : ℝ) ^ (-(49597 / 100000 : ℝ) * (k : ℝ)) := by
  unfold HasWrapSeparation at hfail
  dsimp only at hfail
  push Not at hfail
  obtain ⟨s, hsk, h3lo, h3hi, n₁, hn₁, n₁', hn₁', n₂, hn₂, n₂', hn₂',
    hs1, hs1', hs2, hs2', hm1, hm2, hr1, hr2, hdne⟩ := hfail
  set m : ℕ := (508 * k) / 1000
  set p : ℝ := Real.log 2 / Real.log 3
  set δ : ℝ := (s : ℝ) / (p * (k : ℝ)) - 1
  set ρ : ℝ := 492 / 1000 + δ + 3 / 10 ^ 7 + σ
  set r : ℕ := Nat.ceil (ρ * (k : ℝ))
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hp_pos : 0 < p := by have := log3_two_bounds.1; linarith
  have h3s_eq : (3 : ℝ) ^ s = (2 : ℝ) ^ ((1 + δ) * (k : ℝ)) := by
    have h1 : (1 + δ) * (k : ℝ) = (s : ℝ) / p := by
      dsimp [δ]; field_simp [hp_pos.ne', hk_pos.ne']; ring
    rw [h1]
    have hp_eq : (s : ℝ) / p = (s : ℝ) * Real.log 3 / Real.log 2 := by
      dsimp [p]; field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
        (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne']
    rw [hp_eq, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      mul_div_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
      ← Real.log_pow, Real.exp_log (by positivity)]
  have hδ_lo : -(1 / 10 ^ 7 : ℝ) ≤ δ := by
    have hge := oddCount_ge_of_rpow_le_three_pow h3lo
    dsimp [δ, p] at hge ⊢
    rw [le_sub_iff_add_le, le_div_iff₀ (mul_pos hp_pos hk_pos)]
    linarith
  have hδ_hi : δ < 12 / 1000 := by
    have hlt := oddCount_lt_of_three_pow_lt_rpow h3hi
    dsimp [δ, p] at hlt ⊢
    rw [sub_lt_iff_lt_add, div_lt_iff₀ (mul_pos hp_pos hk_pos)]
    linarith
  have hσ_lo : (1 : ℝ) / 10 ^ 7 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_hi : σ ≤ (1 : ℝ) / 10 ^ 4 := by rcases hσ with rfl | rfl <;> norm_num
  have hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ) := by
    have h1 : 508 * k < 1000 * (m + 1) := by dsimp [m]; omega
    have h1r : (508 : ℝ) * (k : ℝ) < 1000 * ((m : ℝ) + 1) := by exact_mod_cast h1
    linarith
  have hr_ge : ρ * (k : ℝ) ≤ (r : ℝ) := Nat.le_ceil _
  have hr_lt : (r : ℝ) < ρ * (k : ℝ) + 1 := Nat.ceil_lt_add_one (by dsimp [ρ]; nlinarith)
  have hrle : r ≤ k + m := by
    have h1 : (r : ℝ) ≤ (k : ℝ) := by dsimp [ρ] at hr_lt; nlinarith
    have h2 : r ≤ k := by exact_mod_cast h1
    omega
  have hm3 : 3 ≤ m := by dsimp [m]; omega
  set R : ℝ := ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ))
  have hOff_all : ∀ n ∈ twoWindowSurvivors k, oddCount k n = s →
      (affineOffset k n : ℝ) / (3 : ℝ) ^ s ≤ R := by
    intro n hn hs
    rw [← hs]
    apply affineOffset_le_of_prefix_product_lower (by norm_num) k n
    intro i _ hik
    exact (Finset.mem_filter.mp hn).2 i (hik.trans (Nat.le_add_right k _))
  have hdiff_mod : ∀ a b : ℕ, T^[k] a % 2 ^ m = T^[k] b % 2 ^ m →
      ∃ ν : ℤ, (T^[k] b : ℤ) - (T^[k] a : ℤ) = ν * (2 : ℤ) ^ m := by
    intro a b hab
    have h1 : (T^[k] b : ℤ) % (2 : ℤ) ^ m = (T^[k] a : ℤ) % (2 : ℤ) ^ m := by exact_mod_cast hab.symm
    rcases int_dvd_sub_of_emod_eq h1 with ⟨ν, hν⟩
    exact ⟨ν, by rw [hν, mul_comm]⟩
  obtain ⟨ν₁, hν₁⟩ := hdiff_mod n₁ n₁' hm1
  obtain ⟨ν₂, hν₂⟩ := hdiff_mod n₂ n₂' hm2
  set d₁ : ℤ := (n₁' : ℤ) - (n₁ : ℤ)
  set d₂ : ℤ := (n₂' : ℤ) - (n₂ : ℤ)
  have hloc1_raw := shift_center_bound hs1 hs1' hν₁ (hOff_all n₁ hn₁ hs1) (hOff_all n₁' hn₁' hs1')
  have hloc2_raw := shift_center_bound hs2 hs2' hν₂ (hOff_all n₂ hn₂ hs2) (hOff_all n₂' hn₂' hs2')
  have hloc1 : |(d₁ : ℝ) - (ν₁ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R := by
    simpa [d₁] using hloc1_raw
  have hloc2 : |(d₂ : ℝ) - (ν₂ : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R := by
    simpa [d₂] using hloc2_raw
  have hR_le_2k : R ≤ (2 : ℝ) ^ k := by
    have hk_pow := nat_le_two_rpow_small hk
    calc R ≤ (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
          dsimp [R]; nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) by positivity]
      _ ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hk_pow (by positivity)
      _ = (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (2 : ℝ) ^ k := Real.rpow_natCast 2 k
  have hnu_bound : ∀ (a b : ℕ) (ν : ℤ), a ∈ twoWindowSurvivors k → b ∈ twoWindowSurvivors k →
      |(b : ℝ) - (a : ℝ) - (ν : ℝ) * (2 : ℝ) ^ (k + m) / (3 : ℝ) ^ s| ≤ R →
      |(ν : ℝ)| ≤ 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := by
    intro a b ν ha hb hloc
    have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hbI := Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1
    have h1 := shift_index_bound_of_shell haI.1 haI.2 hbI.1 hbI.2 hloc
    have h2 : ((2 : ℝ) ^ k + R) * (3 : ℝ) ^ s / (2 : ℝ) ^ (k + m) ≤ 3 * (3 : ℝ) ^ s / (2 : ℝ) ^ m := by
      rw [pow_add]
      have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have h2mpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      rw [div_le_div_iff₀ (mul_pos h2kpos h2mpos) h2mpos]
      have hR2 : (2 : ℝ) ^ k + R ≤ 3 * (2 : ℝ) ^ k := by linarith
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hR2 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ s)) h2mpos.le
      linarith
    exact h1.trans h2
  have hnu1 := hnu_bound n₁ n₁' ν₁ hn₁ hn₁' hloc1_raw
  have hnu2 := hnu_bound n₂ n₂' ν₂ hn₂ hn₂' hloc2_raw
  have hmod_r : ∃ a : ℤ, d₂ - d₁ = a * (2 : ℤ) ^ r := by
    have h1 : (n₂' : ℤ) % (2 : ℤ) ^ r = (n₁' : ℤ) % (2 : ℤ) ^ r := by exact_mod_cast hr2.symm
    have h2 : (n₂ : ℤ) % (2 : ℤ) ^ r = (n₁ : ℤ) % (2 : ℤ) ^ r := by exact_mod_cast hr1.symm
    have hd1 : (2 : ℤ) ^ r ∣ (n₂' : ℤ) - (n₁' : ℤ) := int_dvd_sub_of_emod_eq h1
    have hd2 : (2 : ℤ) ^ r ∣ (n₂ : ℤ) - (n₁ : ℤ) := int_dvd_sub_of_emod_eq h2
    have hsub : d₂ - d₁ = ((n₂' : ℤ) - (n₁' : ℤ)) - ((n₂ : ℤ) - (n₁ : ℤ)) := by dsimp [d₁, d₂]; ring
    rw [hsub]
    rcases dvd_sub hd1 hd2 with ⟨a, ha⟩
    exact ⟨a, by rw [ha, mul_comm]⟩
  obtain ⟨a, hmod⟩ := hmod_r
  have hsepR : 2 * R < (2 : ℝ) ^ r := by
    have hk_pow := nat_le_two_rpow_small hk
    calc 2 * R = (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by dsimp [R]; ring
      _ ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hk_pow (by positivity)
      _ = (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ < (2 : ℝ) ^ (r : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by dsimp [ρ] at hr_ge; nlinarith)
      _ = (2 : ℝ) ^ r := Real.rpow_natCast 2 r
  obtain ⟨ha_ne, ht_ne, hX_ne, hZ_ne, hXZ_ne, hZX_bound, ht_bound⟩ :=
    wrap_separation_vector_bounds hrle hm3 hdne hmod hloc1 hloc2 hnu1 hnu2 hsepR
  obtain ⟨hH_ok, htp_lt, hX_hi, hZX_ratio⟩ :=
    wrap_failure_primitive_bounds hσ_lo hH₀ hk hrle rfl hm_ge hr_ge rfl
      h3s_eq h3hi ht_ne ha_ne hX_ne hXZ_ne hZX_bound ht_bound
  exact ⟨(ν₂ - ν₁) * (2 : ℤ) ^ (k + m - r), a * (3 : ℤ) ^ s,
    hX_ne, hZ_ne, hXZ_ne, hH_ok, htp_lt, hX_hi, hZX_ratio⟩

/-- Helper: for `z ∈ [1/1024, 1023/1024]`, `-Real.logb 2 z ≤ 10` and `-Real.logb 2 (1 - z) ≤ 10`. -/
private lemma neg_logb2_le_ten {z : ℝ} (hz1 : (1 : ℝ) / 1024 ≤ z) (hz2 : z ≤ 1023 / 1024) :
    -Real.logb 2 z ≤ 10 ∧ -Real.logb 2 (1 - z) ≤ 10 := by
  have h10 : Real.logb 2 ((1 : ℝ) / 1024) = -10 := by
    have hpow : ((1 : ℝ) / 1024) = (2 : ℝ) ^ (-10 : ℝ) := by
      rw [show (-10 : ℝ) = (-10 : ℤ) by norm_num, Real.rpow_intCast]; norm_num
    rw [hpow, Real.logb_rpow (by norm_num) (by norm_num)]
  constructor
  · have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hz1
    linarith
  · have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) (by linarith : (1 : ℝ) / 1024 ≤ 1 - z)
    linarith

/-- Helper: for `q ∈ [1/1024, 1023/1024]`, `(2 : ℝ) ^ (-10 : ℝ) ≤ couplingLambda q`. -/
private lemma couplingLambda_ge_two_neg_ten {q : ℝ} (hq1 : (1 : ℝ) / 1024 ≤ q) (hq2 : q ≤ 1023 / 1024) :
    (2 : ℝ) ^ (-10 : ℝ) ≤ couplingLambda q := by
  unfold couplingLambda
  have hprod : (1 : ℝ) / 1024 * (1 / 1024) ≤ q * (1 - q) :=
    mul_le_mul hq1 (by linarith) (by norm_num) (by linarith)
  have hsqrt : (1 : ℝ) / 1024 ≤ Real.sqrt (q * (1 - q)) := by
    have := Real.sqrt_le_sqrt hprod
    rwa [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 1024)] at this
  have h210 : (2 : ℝ) ^ (-10 : ℝ) = 1 / 1024 := by
    rw [show (-10 : ℝ) = (-10 : ℤ) by norm_num, Real.rpow_intCast]; norm_num
  rw [h210]
  linarith

/-- Helper: exact per-slice far-pair exponent bound `≤ 2^(F * k + 30)`. -/
private lemma slice_far_bound {k r L m sr j : ℕ} {ρ len pref suf x xi q : ℝ}
    {A : Finset ℕ}
    (hrL : r + L = k) (hsr_le_r : sr ≤ r) (hjL : j ≤ L)
    (hAsub_Ico : A ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)))
    (hAsr : ∀ n ∈ A, oddCount r n = sr)
    (hAj : ∀ n ∈ A, suffixOddCount r L n = j)
    (hAsep : ∀ n₁ ∈ A, ∀ n₁' ∈ A, ∀ n₂ ∈ A, ∀ n₂' ∈ A,
      T^[k] n₁ % 2 ^ m = T^[k] n₁' % 2 ^ m → T^[k] n₂ % 2 ^ m = T^[k] n₂' % 2 ^ m →
      n₁ % 2 ^ r = n₂ % 2 ^ r → n₁' % 2 ^ r = n₂' % 2 ^ r →
      (n₁' : ℤ) - (n₁ : ℤ) = (n₂' : ℤ) - (n₂ : ℤ))
    (hx1 : (1 : ℝ) / 1024 ≤ x) (hx2 : x ≤ 1023 / 1024)
    (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hq1 : (1 : ℝ) / 1024 ≤ q) (hq2 : q ≤ 1023 / 1024)
    (hL_ge : len * (k : ℝ) - 1 ≤ (L : ℝ))
    (hce_pref : crossEntropy (r : ℝ) (sr : ℝ) x ≤ crossEntropy ρ pref x * (k : ℝ) + 10)
    (hce_suf : crossEntropy (L : ℝ) (j : ℝ) q ≤ crossEntropy len suf q * (k : ℝ)) :
    let H : ℕ := Nat.ceil (xi * (L : ℝ))
    let F : ℝ := 2 * crossEntropy ρ pref x + xi * len +
      crossEntropy (len - xi * len) (suf - xi * len / 2) q
    (farCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤ (2 : ℝ) ^ (F * (k : ℝ) + 30) := by
  intro H F
  have h1 := card_farCollisions_slice_le (H := H) (q := q) hrL hjL hAsub_Ico hAsr hAj
    (fun n => T^[k] n % 2 ^ m) hAsep (by linarith) (by linarith)
  have hlam_pos : 0 < couplingLambda q := couplingLambda_pos (by linarith) (by linarith)
  have hlam_le1 : couplingLambda q ≤ 1 := couplingLambda_le_one q
  have hH_ge : xi * len * (k : ℝ) - 1 ≤ (H : ℝ) := by
    have hce : xi * (L : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
    nlinarith
  have hlamH : (couplingLambda q) ^ H ≤ (2 : ℝ) ^ (10 : ℝ) * (couplingLambda q) ^ (xi * len * (k : ℝ)) := by
    rw [← Real.rpow_natCast (couplingLambda q) H]
    have hstep1 : (couplingLambda q) ^ (H : ℝ) ≤ (couplingLambda q) ^ (xi * len * (k : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam_le1 hH_ge
    rw [Real.rpow_sub hlam_pos, Real.rpow_one] at hstep1
    have hinv_le : (couplingLambda q)⁻¹ ≤ (2 : ℝ) ^ (10 : ℝ) := by
      have hge := couplingLambda_ge_two_neg_ten hq1 hq2
      have h210 : ((2 : ℝ) ^ (-10 : ℝ))⁻¹ = (2 : ℝ) ^ (10 : ℝ) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
      rw [← h210]
      exact (inv_le_inv₀ hlam_pos (by positivity)).mpr hge
    calc (couplingLambda q) ^ (H : ℝ)
        ≤ (couplingLambda q) ^ (xi * len * (k : ℝ)) * (couplingLambda q)⁻¹ := by
          simpa [div_eq_mul_inv] using hstep1
      _ ≤ (couplingLambda q) ^ (xi * len * (k : ℝ)) * (2 : ℝ) ^ (10 : ℝ) :=
          mul_le_mul_of_nonneg_left hinv_le (by positivity)
      _ = (2 : ℝ) ^ (10 : ℝ) * (couplingLambda q) ^ (xi * len * (k : ℝ)) := mul_comm _ _
  have hlam_rpow : (couplingLambda q) ^ (xi * len * (k : ℝ)) =
      (2 : ℝ) ^ ((xi * len * (k : ℝ)) * Real.logb 2 (couplingLambda q)) := by
    rw [mul_comm (xi * len * (k : ℝ)), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hlam_pos]
  have hbin_sq : (Nat.choose r sr : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * crossEntropy ρ pref x * (k : ℝ) + 20) := by
    have hbi := binom_le_two_rpow_crossEntropy (z := x) hsr_le_r (by linarith) (by linarith)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hbi 2
    rw [← Real.rpow_natCast ((2 : ℝ) ^ _) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hsq
    refine hsq.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    push_cast; linarith
  have hsuf_q : (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q ≤ (2 : ℝ) ^ (crossEntropy len suf q * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hce_suf
  have hmul_all :
      (Nat.choose r sr : ℝ) ^ 2 * (2 : ℝ) ^ crossEntropy (L : ℝ) (j : ℝ) q * (couplingLambda q) ^ H ≤
        (2 : ℝ) ^ (2 * crossEntropy ρ pref x * (k : ℝ) + 20) *
        (2 : ℝ) ^ (crossEntropy len suf q * (k : ℝ)) *
        ((2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ ((xi * len * (k : ℝ)) * Real.logb 2 (couplingLambda q))) := by
    rw [← hlam_rpow]
    exact mul_le_mul (mul_le_mul hbin_sq hsuf_q (by positivity) (by positivity)) hlamH
      (by positivity) (by positivity)
  refine (h1.trans hmul_all).trans (le_of_eq ?_)
  have hassoc : ∀ a b c d : ℝ, a * b * (c * d) = a * b * c * d := fun _ _ _ _ => by ring
  rw [hassoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hid := crossEntropy_far_algebraic_identity (by linarith : 0 < q) (by linarith : q < 1)
    len suf (xi * len / 2)
  have h2t : 2 * (xi * len / 2) = xi * len := by ring
  rw [h2t] at hid
  dsimp [F]
  have hscaled : (crossEntropy len suf q + xi * len * Real.logb 2 (couplingLambda q)) * (k : ℝ) =
      (xi * len + crossEntropy (len - xi * len) (suf - xi * len / 2) q) * (k : ℝ) := by
    rw [hid]
  linarith

/-- Helper: binomial switch sum bound for `slice_near_bound`. -/
private lemma slice_near_binom_sum {k L j H : ℕ} {len suf xi w₁ w₀ : ℝ}
    (hLk : L ≤ k)
    (hH : H = Nat.ceil (xi * (L : ℝ)))
    (hxi0 : 0 < xi)
    (hw11 : (1 : ℝ) / 1024 ≤ w₁) (hw12 : w₁ ≤ 1023 / 1024)
    (hw01 : (1 : ℝ) / 1024 ≤ w₀) (hw02 : w₀ ≤ 1023 / 1024) (hwsum : w₁ + w₀ ≤ 1)
    (hL_le : (L : ℝ) ≤ len * (k : ℝ))
    (hj_le : (j : ℝ) ≤ suf * (k : ℝ))
    (hLj_le : ((L - j : ℕ) : ℝ) ≤ (len - suf) * (k : ℝ)) :
    ∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
      ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ) ≤
    ((k : ℝ) + 1) * (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
      crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) := by
  have hterm : ∀ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
      ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
          crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) := by
    intro i hi
    by_cases hle : i ≤ j ∧ i ≤ L - j
    · have h2i_lt : (2 * i : ℝ) < xi * (L : ℝ) := by
        have hlt : 2 * i < Nat.ceil (xi * (L : ℝ)) := by rw [← hH]; exact (Finset.mem_filter.mp hi).2
        have := Nat.lt_ceil.mp hlt
        push_cast at this ⊢; exact this
      have hi_le_tk : (i : ℝ) ≤ (xi * len / 2) * (k : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hL_le hxi0.le
        linarith only [h2i_lt, hmul]
      have hbi1 := binom_le_two_rpow_crossEntropy hle.1 (by linarith only [hw11] : 0 < w₁) (by linarith only [hw12] : w₁ < 1)
      have hbi2 := binom_le_two_rpow_crossEntropy hle.2 (by linarith only [hw01] : 0 < w₀) (by linarith only [hw02] : w₀ < 1)
      have hmul := mul_le_mul hbi1 hbi2 (Nat.cast_nonneg _) (by positivity)
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hmul
      rw [Nat.cast_mul]
      refine hmul.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
      have hslope_nonneg : 0 ≤ (-Real.logb 2 w₁ - -Real.logb 2 (1 - w₁)) +
          (-Real.logb 2 w₀ - -Real.logb 2 (1 - w₀)) := by
        have hprod_le : w₁ * w₀ ≤ (1 - w₁) * (1 - w₀) := by nlinarith only [hwsum]
        have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (mul_pos (by linarith only [hw11]) (by linarith only [hw01])) hprod_le
        rw [Real.logb_mul (by linarith only [hw11]) (by linarith only [hw01]),
          Real.logb_mul (by linarith only [hw12]) (by linarith only [hw02])] at hlog
        linarith only [hlog]
      have hnl_1w1 : 0 ≤ -Real.logb 2 (1 - w₁) := by
        have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith only [hw12] : (0 : ℝ) ≤ 1 - w₁) (by linarith only [hw11] : 1 - w₁ ≤ 1)
        linarith only [this]
      have hnl_1w0 : 0 ≤ -Real.logb 2 (1 - w₀) := by
        have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith only [hw02] : (0 : ℝ) ≤ 1 - w₀) (by linarith only [hw01] : 1 - w₀ ≤ 1)
        linarith only [this]
      unfold crossEntropy
      have hs1 := mul_le_mul_of_nonneg_right hi_le_tk hslope_nonneg
      have hs2 := mul_le_mul_of_nonneg_right hj_le hnl_1w1
      have hs3 := mul_le_mul_of_nonneg_right hLj_le hnl_1w0
      linarith only [hs1, hs2, hs3]
    · have h0 : Nat.choose j i * Nat.choose (L - j) i = 0 := by
        rcases not_and_or.mp hle with h | h
        · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h), zero_mul]
        · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h), mul_zero]
      rw [h0, Nat.cast_zero]; positivity
  calc ∑ i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          ((Nat.choose j i * Nat.choose (L - j) i : ℕ) : ℝ)
      ≤ ∑ _i ∈ (Finset.range (L + 1)).filter (fun i => 2 * i < H),
          (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
            crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) := Finset.sum_le_sum hterm
    _ = (((Finset.range (L + 1)).filter (fun i => 2 * i < H)).card : ℝ) *
          (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
            crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
          crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard_le : ((Finset.range (L + 1)).filter (fun i => 2 * i < H)).card ≤ k + 1 := by
          calc _ ≤ (Finset.range (L + 1)).card := Finset.card_filter_le _ _
            _ = L + 1 := Finset.card_range _
            _ ≤ k + 1 := by omega
        exact_mod_cast hcard_le

/-- Helper: exact per-slice near-pair exponent bound `≤ 13 * (k + 1)^2 * 2^(N * k + 10)`. -/
private lemma slice_near_bound {k r L m sr j : ℕ} {ρ len suf d_r U xi w₁ w₀ : ℝ}
    {A : Finset ℕ}
    (hk : 2 ^ 40 ≤ k) (hrL : r + L = k)
    (hm_eq : m = (508 * k) / 1000)
    (hAsub : A ⊆ twoWindowSurvivors k)
    (hAsr : ∀ n ∈ A, oddCount r n = sr)
    (hAj : ∀ n ∈ A, suffixOddCount r L n = j)
    (hA_direct : (A.card : ℝ) ≤ (2 : ℝ) ^ (U * (k : ℝ) + 10))
    (hxi0 : 0 < xi)
    (hw11 : (1 : ℝ) / 1024 ≤ w₁) (hw12 : w₁ ≤ 1023 / 1024)
    (hw01 : (1 : ℝ) / 1024 ≤ w₀) (hw02 : w₀ ≤ 1023 / 1024) (hwsum : w₁ + w₀ ≤ 1)
    (hlen : len = 1 - ρ)
    (hL_ge : len * (k : ℝ) - 1 ≤ (L : ℝ)) (hL_le : (L : ℝ) ≤ len * (k : ℝ))
    (hj_le : (j : ℝ) ≤ suf * (k : ℝ))
    (hLj_le : ((L - j : ℕ) : ℝ) ≤ (len - suf) * (k : ℝ))
    (hdr_eq : d_r = (sr : ℝ) / ((Real.log 2 / Real.log 3) * (k : ℝ)) - (r : ℝ) / (k : ℝ)) :
    let H : ℕ := Nat.ceil (xi * (L : ℝ))
    let N : ℝ := U + crossEntropy suf (xi * len / 2) w₁ +
      crossEntropy (len - suf) (xi * len / 2) w₀ +
      max 0 (ρ + d_r - 508 / 1000) + 1 / 10 ^ 7
    (nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
      13 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (N * (k : ℝ) + 10) := by
  intro H N
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hrk : r ≤ k := by omega
  set p : ℝ := Real.log 2 / Real.log 3
  have hp_pos : 0 < p := by have := log3_two_bounds.1; linarith
  set R_r : ℝ := ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ))
  set U_y : ℕ := Nat.floor (3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ)))
  have hOff_r : ∀ n ∈ A, (affineOffset r n : ℝ) / (3 : ℝ) ^ sr ≤ R_r := by
    intro n hn
    have hnS := hAsub hn
    rw [← hAsr n hn]
    have h1 := affineOffset_le_of_prefix_product_lower (by norm_num) r n
      (fun i _ hir => (Finset.mem_filter.mp hnS).2 i ((hir.trans hrk).trans (Nat.le_add_right k _)))
    have hr_le : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
    have h2 : (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (r : ℝ)) ≤ (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hr_le (by norm_num))
    dsimp [R_r]
    exact h1.trans (mul_le_mul (by linarith) h2 (by positivity) (by positivity))
  have hUy : ∀ n ∈ A, T^[r] n ≤ U_y := by
    intro n hn
    have hnI := Finset.mem_Ico.mp (Finset.mem_filter.mp (hAsub hn)).1
    have haff : (2 : ℝ) ^ r * (T^[r] n : ℝ) = (3 : ℝ) ^ sr * (n : ℝ) + (affineOffset r n : ℝ) := by
      have := two_pow_mul_iterate r n; rw [hAsr n hn] at this; exact_mod_cast this
    have h3sr_eq : (3 : ℝ) ^ sr / (2 : ℝ) ^ r = (2 : ℝ) ^ (d_r * (k : ℝ)) := by
      have h1 : d_r * (k : ℝ) = (sr : ℝ) / p - (r : ℝ) := by
        rw [hdr_eq]; field_simp [hp_pos.ne', hk_pos.ne']
      rw [h1, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      congr 1
      have hp_eq : (sr : ℝ) / p = (sr : ℝ) * Real.log 3 / Real.log 2 := by
        dsimp [p]; field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
          (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne']
      rw [hp_eq, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        mul_div_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
        ← Real.log_pow, Real.exp_log (by positivity)]
    have hTr_eq : (T^[r] n : ℝ) = (2 : ℝ) ^ (d_r * (k : ℝ)) * ((n : ℝ) + (affineOffset r n : ℝ) / (3 : ℝ) ^ sr) := by
      rw [← h3sr_eq]
      field_simp [(by positivity : (0 : ℝ) < (2 : ℝ) ^ r).ne', (by positivity : (0 : ℝ) < (3 : ℝ) ^ sr).ne']
      linarith
    have hRr_le : R_r ≤ (2 : ℝ) ^ k := by
      have hk_pow := nat_le_two_rpow_small hk
      calc R_r ≤ (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
            dsimp [R_r]; nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) by positivity]
        _ ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hk_pow (by positivity)
        _ = (2 : ℝ) ^ ((4 / 10 ^ 9 + 1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
        _ ≤ (2 : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = (2 : ℝ) ^ k := Real.rpow_natCast 2 k
    have hn_lt : (n : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
      have : (n : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hnI.2
      rw [pow_succ] at this; linarith
    have hTr_le : (T^[r] n : ℝ) ≤ 3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ)) := by
      rw [hTr_eq]
      have hsum : (n : ℝ) + (affineOffset r n : ℝ) / (3 : ℝ) ^ sr ≤ 3 * (2 : ℝ) ^ k := by
        linarith [hOff_r n hn]
      calc (2 : ℝ) ^ (d_r * (k : ℝ)) * ((n : ℝ) + (affineOffset r n : ℝ) / (3 : ℝ) ^ sr)
          ≤ (2 : ℝ) ^ (d_r * (k : ℝ)) * (3 * (2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 3 * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (d_r * (k : ℝ))) := by rw [Real.rpow_natCast]; ring
        _ = 3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 2; ring
    exact Nat.le_floor hTr_le
  have h1 := card_nearCollisions_slice_le (m := m) (H := H) hrL (by positivity : 0 ≤ R_r) hAsr hAj hUy hOff_r
  have hbin_sum := slice_near_binom_sum (by omega : L ≤ k) rfl hxi0 hw11 hw12 hw01 hw02 hwsum
    hL_le hj_le hLj_le
  have hInt_le : ((U_y / 2 ^ (L + m) + 1 : ℕ) : ℝ) ≤
      13 * (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) := by
    have hdiv_le : ((U_y / 2 ^ (L + m) : ℕ) : ℝ) ≤ (U_y : ℝ) / (2 : ℝ) ^ (L + m) := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self U_y (2 ^ (L + m))
    have hUy_le : (U_y : ℝ) ≤ 3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ)) := Nat.floor_le (by positivity)
    have hLm_ge : (1 - ρ + 508 / 1000) * (k : ℝ) - 2 ≤ ((L + m : ℕ) : ℝ) := by
      have hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ) := by
        have h1' : 508 * k < 1000 * (m + 1) := by omega
        have h1r : (508 : ℝ) * (k : ℝ) < 1000 * ((m : ℝ) + 1) := by exact_mod_cast h1'
        linarith
      push_cast; rw [hlen] at hL_ge; linarith
    have h2Lm : (2 : ℝ) ^ ((1 - ρ + 508 / 1000) * (k : ℝ) - 2) ≤ (2 : ℝ) ^ (L + m) := by
      rw [← Real.rpow_natCast (2 : ℝ) (L + m)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hLm_ge
    have hq_le : (U_y : ℝ) / (2 : ℝ) ^ (L + m) ≤ 12 * (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) := by
      calc (U_y : ℝ) / (2 : ℝ) ^ (L + m)
          ≤ (3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ))) / (2 : ℝ) ^ ((1 - ρ + 508 / 1000) * (k : ℝ) - 2) :=
            div_le_div₀ (by positivity) hUy_le (by positivity) h2Lm
        _ = 3 * (2 : ℝ) ^ ((1 + d_r) * (k : ℝ) - ((1 - ρ + 508 / 1000) * (k : ℝ) - 2)) := by
            rw [mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        _ = 12 * (2 : ℝ) ^ ((ρ + d_r - 508 / 1000) * (k : ℝ)) := by
            have : (1 + d_r) * (k : ℝ) - ((1 - ρ + 508 / 1000) * (k : ℝ) - 2) =
                2 + (ρ + d_r - 508 / 1000) * (k : ℝ) := by ring
            rw [this, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num; ring
        _ ≤ 12 * (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hk_pos.le)
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (le_max_left _ _) hk_pos.le)
    push_cast; linarith
  have hRr1_le : R_r + 1 ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) := by
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hhalf : ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) ≤
        (k : ℝ) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [hk_pos]) (by positivity)
    dsimp [R_r]; linarith [hge1, hhalf]
  have hcomb := mul_le_mul (mul_le_mul (mul_le_mul hA_direct hbin_sum
    (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity))
    hInt_le (by positivity) (by positivity)) hRr1_le (by positivity) (by positivity)
  refine (h1.trans hcomb).trans (le_of_eq ?_)
  have hexp :
      (2 : ℝ) ^ (U * (k : ℝ) + 10) *
        (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
          crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) *
        (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) *
        (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)) =
      (2 : ℝ) ^ (N * (k : ℝ) + 10) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; dsimp [N]; ring
  calc (2 : ℝ) ^ (U * (k : ℝ) + 10) *
          (((k : ℝ) + 1) * (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
            crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ))) *
          (13 * (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ))) *
          (((k : ℝ) + 1) * (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ)))
      = 13 * ((k : ℝ) + 1) ^ 2 *
          ((2 : ℝ) ^ (U * (k : ℝ) + 10) *
            (2 : ℝ) ^ ((crossEntropy suf (xi * len / 2) w₁ +
              crossEntropy (len - suf) (xi * len / 2) w₀) * (k : ℝ)) *
            (2 : ℝ) ^ (max 0 (ρ + d_r - 508 / 1000) * (k : ℝ)) *
            (2 : ℝ) ^ ((1 / 10 ^ 7 : ℝ) * (k : ℝ))) := by ring
    _ = 13 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (N * (k : ℝ) + 10) := by rw [hexp]

/-- Helper: collision branch of `good_shell_single_slice_le` combining `slice_far_bound`,
`slice_near_bound`, and `card_sq_le_card_mul_collisions`. -/
private lemma good_shell_slice_collision_branch {σ v δ ρ len pref suf d_r U N F M₂ x xi w₁ w₀ q z₂ : ℝ}
    {k r L m s sr j : ℕ} {A : Finset ℕ}
    (hk : 2 ^ 40 ≤ k) (hrL : r + L = k) (hm_eq : m = (508 * k) / 1000)
    (hsk : s ≤ k) (hsr_le_r : sr ≤ r) (hjL : j ≤ L)
    (h3lo : (2 : ℝ) ^ ((1 - (1 : ℝ) / 10 ^ 7) * (k : ℝ)) ≤ (3 : ℝ) ^ s)
    (h3hi : (3 : ℝ) ^ s < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)))
    (hsep : HasWrapSeparation σ k)
    (hAsub_S : A ⊆ twoWindowSurvivors k)
    (hAs : ∀ n ∈ A, oddCount k n = s)
    (hAsr : ∀ n ∈ A, oddCount r n = sr)
    (hAj : ∀ n ∈ A, suffixOddCount r L n = j)
    (hA_direct : (A.card : ℝ) ≤ (2 : ℝ) ^ (U * (k : ℝ) + 10))
    (hx1 : (1 : ℝ) / 1024 ≤ x) (hx2 : x ≤ 1023 / 1024)
    (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hw11 : (1 : ℝ) / 1024 ≤ w₁) (hw12 : w₁ ≤ 1023 / 1024)
    (hw01 : (1 : ℝ) / 1024 ≤ w₀) (hw02 : w₀ ≤ 1023 / 1024) (hwsum : w₁ + w₀ ≤ 1)
    (hq1 : (1 : ℝ) / 1024 ≤ q) (hq2 : q ≤ 1023 / 1024)
    (hz21 : (1 : ℝ) / 2 ≤ z₂) (hz22 : z₂ ≤ 1023 / 1024)
    (hδ_eq : δ = (s : ℝ) / ((Real.log 2 / Real.log 3) * (k : ℝ)) - 1)
    (hr_eq : r = Nat.ceil ((492 / 1000 + δ + 3 / 10 ^ 7 + σ) * (k : ℝ)))
    (hlen : len = 1 - ρ)
    (hL_ge : len * (k : ℝ) - 1 ≤ (L : ℝ)) (hL_le : (L : ℝ) ≤ len * (k : ℝ))
    (hj_le : (j : ℝ) ≤ suf * (k : ℝ))
    (hLj_le : ((L - j : ℕ) : ℝ) ≤ (len - suf) * (k : ℝ))
    (hdr_eq : d_r = (sr : ℝ) / ((Real.log 2 / Real.log 3) * (k : ℝ)) - (r : ℝ) / (k : ℝ))
    (hce_pref : crossEntropy (r : ℝ) (sr : ℝ) x ≤ crossEntropy ρ pref x * (k : ℝ) + 10)
    (hce_suf : crossEntropy (L : ℝ) (j : ℝ) q ≤ crossEntropy len suf q * (k : ℝ))
    (hN_eq : N = U + crossEntropy suf (xi * len / 2) w₁ +
      crossEntropy (len - suf) (xi * len / 2) w₀ +
      max 0 (ρ + d_r - 508 / 1000) + 1 / 10 ^ 7)
    (hF_eq : F = 2 * crossEntropy ρ pref x + xi * len +
      crossEntropy (len - xi * len) (suf - xi * len / 2) q)
    (hM2_eq : M₂ = crossEntropy (508 / 1000)
      ((Real.log 2 / Real.log 3) * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂)
    (hNM_lt : (N + M₂) / 2 < v) (hFM_lt : (F + M₂) / 2 < v) :
    (A.card : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ)) := by
  classical
  set p : ℝ := Real.log 2 / Real.log 3
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hp_lo := log3_two_bounds.1
  have hp_hi := log3_two_bounds.2
  have hp_pos : 0 < p := by linarith
  set s'_real : ℝ := p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000)) * (k : ℝ)
  set Z_s : Finset ℕ := (Finset.range (2 ^ m)).filter (fun y => s'_real - 1 ≤ (oddCount m y : ℝ))
  have hA_to_Zs : ∀ n ∈ A, T^[k] n % 2 ^ m ∈ Z_s := by
    intro n hn
    have hnS := hAsub_S hn
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)), ?_⟩
    rw [oddCount_mod]
    have hadd := oddCount_add k m n
    have hkm := (Finset.mem_filter.mp hnS).2 (k + m) (by rw [hm_eq])
    have hge := oddCount_ge_of_rpow_le_three_pow hkm
    rw [hadd, hAs n hn] at hge
    have hs_ex : (s : ℝ) = p * (1 + δ) * (k : ℝ) := by
      rw [hδ_eq]; field_simp [hp_pos.ne', hk_pos.ne']; ring
    have hm_ge : (508 / 1000 : ℝ) * (k : ℝ) - 1 ≤ (m : ℝ) := by
      have h1 : 508 * k < 1000 * (m + 1) := by omega
      have h1r : (508 : ℝ) * (k : ℝ) < 1000 * ((m : ℝ) + 1) := by exact_mod_cast h1
      linarith
    have hstep1 : p * ((1 - (1 : ℝ) / 10 ^ 7) * ((k : ℝ) + ((508 / 1000 : ℝ) * (k : ℝ) - 1))) ≤
        p * ((1 - (1 : ℝ) / 10 ^ 7) * ((k : ℝ) + (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hm_ge]) (by norm_num)) hp_pos.le
    have hstep2 : s'_real - 1 + (s : ℝ) ≤
        p * ((1 - (1 : ℝ) / 10 ^ 7) * ((k : ℝ) + ((508 / 1000 : ℝ) * (k : ℝ) - 1))) := by
      rw [hs_ex]; dsimp [s'_real]
      have hpl1 : p * (1 - (1 : ℝ) / 10 ^ 7) ≤ 1 := by linarith [hp_hi]
      have hid : p * ((1 - (1 : ℝ) / 10 ^ 7) * ((k : ℝ) + ((508 / 1000 : ℝ) * (k : ℝ) - 1))) -
          (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000)) * (k : ℝ) - 1 + p * (1 + δ) * (k : ℝ)) =
          1 - p * (1 - (1 : ℝ) / 10 ^ 7) := by ring
      linarith [hid, hpl1]
    push_cast at hge
    change p * ((1 - (1 : ℝ) / 10 ^ 7) * ((k : ℝ) + (m : ℝ))) ≤ (s : ℝ) + (oddCount m (T^[k] n) : ℝ) at hge
    linarith [hstep1, hstep2, hge]
  have hZs_card : (Z_s.card : ℝ) ≤ (2 : ℝ) ^ (M₂ * (k : ℝ) + 10) := by
    have h1 := card_residue_menu_le (m := m) (s₀ := s'_real - 1) hz21 (by linarith)
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hm_le : (m : ℝ) ≤ (508 / 1000 : ℝ) * (k : ℝ) := by
      have h1' : 1000 * m ≤ 508 * k := by omega
      have h1r : (1000 : ℝ) * (m : ℝ) ≤ 508 * (k : ℝ) := by exact_mod_cast h1'
      linarith
    have hlog_z2 := neg_logb2_le_ten (by linarith) hz22
    have hnl_nonneg : 0 ≤ -Real.logb 2 (1 - z₂) := by
      have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith : (0 : ℝ) ≤ 1 - z₂) (by linarith : 1 - z₂ ≤ 1); linarith
    have hnl_z2_nonneg : 0 ≤ -Real.logb 2 z₂ := by
      have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith : (0 : ℝ) ≤ z₂) (by linarith : z₂ ≤ 1); linarith
    have hdm := mul_le_mul_of_nonneg_right hm_le hnl_nonneg
    rw [show M₂ * (k : ℝ) = crossEntropy ((508 / 1000 : ℝ) * (k : ℝ)) s'_real z₂ by
      rw [hM2_eq]; dsimp [s'_real, p]; unfold crossEntropy; ring]
    unfold crossEntropy
    linarith [hdm, hlog_z2.1, hlog_z2.2, hnl_z2_nonneg]
  have hAsub_Ico : A ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := fun n hn => (Finset.mem_filter.mp (hAsub_S hn)).1
  have hAsep : ∀ n₁ ∈ A, ∀ n₁' ∈ A, ∀ n₂ ∈ A, ∀ n₂' ∈ A,
      T^[k] n₁ % 2 ^ m = T^[k] n₁' % 2 ^ m → T^[k] n₂ % 2 ^ m = T^[k] n₂' % 2 ^ m →
      n₁ % 2 ^ r = n₂ % 2 ^ r → n₁' % 2 ^ r = n₂' % 2 ^ r →
      (n₁' : ℤ) - (n₁ : ℤ) = (n₂' : ℤ) - (n₂ : ℤ) := by
    intro n₁ hn₁ n₁' hn₁' n₂ hn₂ n₂' hn₂' hm1 hm2 hr1 hr2
    have hsep' := hsep s hsk h3lo h3hi n₁ (hAsub_S hn₁) n₁' (hAsub_S hn₁') n₂ (hAsub_S hn₂) n₂' (hAsub_S hn₂')
      (hAs n₁ hn₁) (hAs n₁' hn₁') (hAs n₂ hn₂) (hAs n₂' hn₂')
    rw [← hm_eq] at hsep'
    rw [← hδ_eq, ← hr_eq] at hsep'
    exact hsep' hm1 hm2 hr1 hr2
  set H : ℕ := Nat.ceil (xi * (L : ℝ))
  have hFar_le : (farCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤ (2 : ℝ) ^ (F * (k : ℝ) + 30) := by
    rw [hF_eq]
    exact slice_far_bound hrL hsr_le_r hjL hAsub_Ico hAsr hAj hAsep hx1 hx2 hxi0 hxi1 hq1 hq2
      hL_ge hce_pref hce_suf
  have hNear_le : (nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
      13 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (N * (k : ℝ) + 10) := by
    rw [hN_eq]
    exact slice_near_bound hk hrL hm_eq hAsub_S hAsr hAj hA_direct hxi0 hw11 hw12 hw01 hw02 hwsum
      hlen hL_ge hL_le hj_le hLj_le hdr_eq
  have hCS : (A.card : ℝ) ^ 2 ≤ (Z_s.card : ℝ) *
      ((nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) +
       (farCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ)) := by
    have hnat := card_sq_le_card_mul_collisions A Z_s (fun n => T^[k] n % 2 ^ m) hA_to_Zs
    rw [collisionCount_eq_near_add_far A _ r L H] at hnat
    exact_mod_cast hnat
  have hNF_le :
      (nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) +
        (farCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
      (2 : ℝ) ^ (31 : ℝ) * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ)) := by
    have h1 : (2 : ℝ) ^ (N * (k : ℝ) + 10) ≤ (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (max N F * (k : ℝ)) := by
      rw [add_comm, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (le_max_left _ _) hk_pos.le))
        (by positivity)
    have h2 : (2 : ℝ) ^ (F * (k : ℝ) + 30) ≤ (2 : ℝ) ^ (30 : ℝ) * (2 : ℝ) ^ (max N F * (k : ℝ)) := by
      rw [add_comm, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (le_max_right _ _) hk_pos.le))
        (by positivity)
    have h13 : 13 * (2 : ℝ) ^ (10 : ℝ) + (2 : ℝ) ^ (30 : ℝ) ≤ (2 : ℝ) ^ (31 : ℝ) := by norm_num
    have hk1sq : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [hk_pos])
    have hNF1 : (nearCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
        (13 * (2 : ℝ) ^ (10 : ℝ)) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) := by
      calc _ ≤ 13 * ((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (max N F * (k : ℝ))) :=
            hNear_le.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
        _ = (13 * (2 : ℝ) ^ (10 : ℝ)) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) := by ring
    have hNF2 : (farCollisions A (fun n => T^[k] n % 2 ^ m) r L H : ℝ) ≤
        (2 : ℝ) ^ (30 : ℝ) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) := by
      calc _ ≤ (2 : ℝ) ^ (30 : ℝ) * (2 : ℝ) ^ (max N F * (k : ℝ)) := hFar_le.trans h2
        _ ≤ (2 : ℝ) ^ (30 : ℝ) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hk1sq) (by positivity)
    have hsum := add_le_add hNF1 hNF2
    have hfac : (13 * (2 : ℝ) ^ (10 : ℝ) + (2 : ℝ) ^ (30 : ℝ)) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) ≤
        (2 : ℝ) ^ (31 : ℝ) * (((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right h13 (by positivity)
    linarith [hsum, hfac]
  have hAsq_le : (A.card : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ))) ^ 2 := by
    have hmul := mul_le_mul hZs_card hNF_le (by positivity) (by positivity)
    have hmax_lt : max N F + M₂ < 2 * v := by
      rcases max_choice N F with h | h <;> rw [h] <;> linarith only [hNM_lt, hFM_lt]
    have hrpow_le : (2 : ℝ) ^ (M₂ * (k : ℝ) + 10) * (2 : ℝ) ^ (max N F * (k : ℝ)) ≤
        (2 : ℝ) ^ (10 : ℝ) * ((2 : ℝ) ^ (v * (k : ℝ))) ^ 2 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_natCast ((2 : ℝ) ^ (v * (k : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      have hmk := mul_lt_mul_of_pos_right hmax_lt hk_pos
      linarith only [hmk]
    have h2_41 : (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (31 : ℝ) ≤ ((2 : ℝ) ^ (30 : ℝ)) ^ 2 := by norm_num
    calc (A.card : ℝ) ^ 2
        ≤ (2 : ℝ) ^ (M₂ * (k : ℝ) + 10) *
            ((2 : ℝ) ^ (31 : ℝ) * ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (max N F * (k : ℝ))) := hCS.trans hmul
      _ = (2 : ℝ) ^ (31 : ℝ) * ((k : ℝ) + 1) ^ 2 *
            ((2 : ℝ) ^ (M₂ * (k : ℝ) + 10) * (2 : ℝ) ^ (max N F * (k : ℝ))) := by ring
      _ ≤ (2 : ℝ) ^ (31 : ℝ) * ((k : ℝ) + 1) ^ 2 *
            ((2 : ℝ) ^ (10 : ℝ) * ((2 : ℝ) ^ (v * (k : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hrpow_le (by positivity)
      _ = ((2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (31 : ℝ)) * (((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (v * (k : ℝ))) ^ 2) := by ring
      _ ≤ ((2 : ℝ) ^ (30 : ℝ)) ^ 2 * (((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (v * (k : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_right h2_41 (by positivity)
      _ = ((2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ))) ^ 2 := by ring
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hRHS_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith [hk_pos]))
      (Real.rpow_nonneg (by norm_num) _)
  nlinarith only [hAsq_le, hA_nn, hRHS_nn]

/-- Helper: per-slice cardinality bound `|Slice s sr| ≤ 2^30 * (k + 1) * 2^(v * k)` under
wrap separation and the uniform slice-exponent certificate. -/
private lemma good_shell_single_slice_le {σ v : ℝ} {k s sr : ℕ}
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 10 ^ 4)
    (hk : 2 ^ 40 ≤ k)
    (hsep : HasWrapSeparation σ k)
    (hcert : ∀ δ d_r : ℝ,
      -(1 / 10 ^ 7 : ℝ) ≤ δ ∧ δ ≤ 12 / 1000 →
      -(1 / 10 ^ 7 : ℝ) ≤ d_r ∧ d_r ≤ 1 →
      let p := Real.log 2 / Real.log 3
      let rho := 492 / 1000 + δ + 3 / 10 ^ 7 + σ
      let len := 1 - rho
      let pref := p * (rho + d_r)
      let suf := p * (1 + δ) - pref
      ∃ x y xi w₁ w₀ q z₂ : ℝ,
        (1 : ℝ) / 1024 ≤ x ∧ x ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ y ∧ y ≤ 1023 / 1024 ∧
        0 < xi ∧ xi < 1 ∧
        (1 : ℝ) / 1024 ≤ w₁ ∧ w₁ ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ w₀ ∧ w₀ ≤ 1023 / 1024 ∧ w₁ + w₀ ≤ 1 ∧
        (1 : ℝ) / 1024 ≤ q ∧ q ≤ 1023 / 1024 ∧
        (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 1023 / 1024 ∧
        let U := crossEntropy rho pref x + crossEntropy len suf y
        let N := U + crossEntropy suf (xi * len / 2) w₁ +
          crossEntropy (len - suf) (xi * len / 2) w₀ +
          max 0 (rho + d_r - 508 / 1000) + 1 / 10 ^ 7
        let F := 2 * crossEntropy rho pref x + xi * len +
          crossEntropy (len - xi * len) (suf - xi * len / 2) q
        let M₂ := crossEntropy (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂
        min U (max ((N + M₂) / 2) ((F + M₂) / 2)) < v) :
    let p : ℝ := Real.log 2 / Real.log 3
    let r : ℕ := Nat.ceil ((492 / 1000 + ((s : ℝ) / (p * (k : ℝ)) - 1) + 3 / 10 ^ 7 + σ) * (k : ℝ))
    let Mid := (twoWindowSurvivors k).filter
      (fun n => (3 : ℝ) ^ oddCount k n < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)))
    let A := Mid.filter (fun n => oddCount k n = s ∧ oddCount r n = sr)
    (A.card : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ)) := by
  classical
  intro p r Mid A
  set m : ℕ := (508 * k) / 1000
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hp_lo := log3_two_bounds.1
  have hp_hi := log3_two_bounds.2
  have hp_pos : 0 < p := by linarith
  have h1p_pos : 0 < 1 - p := by linarith
  by_cases hemp : A.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hemp
    have hn₀' := Finset.mem_filter.mp hn₀
    have hn₀M := Finset.mem_filter.mp hn₀'.1
    have hn₀S := hn₀M.1
    have hs_eq : oddCount k n₀ = s := hn₀'.2.1
    have hsr_eq : oddCount r n₀ = sr := hn₀'.2.2
    have hsk : s ≤ k := by rw [← hs_eq]; exact oddCount_le k n₀
    have h3lo : (2 : ℝ) ^ ((1 - (1 : ℝ) / 10 ^ 7) * (k : ℝ)) ≤ (3 : ℝ) ^ s := by
      rw [← hs_eq]; exact (Finset.mem_filter.mp hn₀S).2 k (Nat.le_add_right k _)
    have h3hi : (3 : ℝ) ^ s < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) := by
      rw [← hs_eq]; exact hn₀M.2
    set δ : ℝ := (s : ℝ) / (p * (k : ℝ)) - 1
    set ρ : ℝ := 492 / 1000 + δ + 3 / 10 ^ 7 + σ
    set len : ℝ := 1 - ρ
    set L : ℕ := k - r
    set j : ℕ := s - sr
    have hδ_lo : -(1 / 10 ^ 7 : ℝ) ≤ δ := by
      have hge := oddCount_ge_of_rpow_le_three_pow h3lo
      dsimp [δ, p] at hge ⊢; rw [le_sub_iff_add_le, le_div_iff₀ (mul_pos hp_pos hk_pos)]; linarith
    have hδ_hi : δ ≤ 12 / 1000 := by
      have hlt := oddCount_lt_of_three_pow_lt_rpow h3hi
      dsimp [δ, p] at hlt ⊢; rw [sub_le_iff_le_add, div_le_iff₀ (mul_pos hp_pos hk_pos)]; linarith
    have hr_eq : r = Nat.ceil (ρ * (k : ℝ)) := rfl
    have hr_ge : ρ * (k : ℝ) ≤ (r : ℝ) := by rw [hr_eq]; exact Nat.le_ceil _
    have hr_lt : (r : ℝ) < ρ * (k : ℝ) + 1 := by
      rw [hr_eq]; exact Nat.ceil_lt_add_one (by dsimp [ρ]; nlinarith)
    have hrk : r ≤ k := by
      have : (r : ℝ) ≤ (k : ℝ) := by dsimp [ρ] at hr_lt; nlinarith
      exact_mod_cast this
    have hrL : r + L = k := Nat.add_sub_of_le hrk
    have hsr_le_r : sr ≤ r := by rw [← hsr_eq]; exact oddCount_le r n₀
    have hsr_le_s : sr ≤ s := by rw [← hsr_eq, ← hs_eq]; exact oddCount_mono hrk n₀
    have hjL : j ≤ L := by
      have hadd := oddCount_add r L n₀; rw [hrL, hs_eq, hsr_eq] at hadd
      have hle := oddCount_le L (T^[r] n₀); omega
    set d_r : ℝ := (sr : ℝ) / (p * (k : ℝ)) - (r : ℝ) / (k : ℝ)
    have hdr_lo : -(1 / 10 ^ 7 : ℝ) ≤ d_r := by
      have h3sr : (2 : ℝ) ^ ((1 - (1 : ℝ) / 10 ^ 7) * (r : ℝ)) ≤ (3 : ℝ) ^ sr := by
        rw [← hsr_eq]; exact (Finset.mem_filter.mp hn₀S).2 r (hrk.trans (Nat.le_add_right k _))
      have hge := oddCount_ge_of_rpow_le_three_pow h3sr
      have hr_le_k : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
      have h1 : d_r = ((sr : ℝ) - p * (r : ℝ)) / (p * (k : ℝ)) := by
        dsimp [d_r]; field_simp [hp_pos.ne', hk_pos.ne']
      have h2 : -(1 / 10 ^ 7 : ℝ) * (p * (k : ℝ)) ≤ (sr : ℝ) - p * (r : ℝ) := by
        dsimp [p] at hge ⊢; nlinarith
      rw [h1, le_div_iff₀ (mul_pos hp_pos hk_pos)]; linarith
    have hdr_hi : d_r ≤ 1 := by
      have h1 : (sr : ℝ) ≤ (r : ℝ) := by exact_mod_cast hsr_le_r
      have h2 : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
      have h3 : d_r = ((sr : ℝ) - p * (r : ℝ)) / (p * (k : ℝ)) := by
        dsimp [d_r]; field_simp [hp_pos.ne', hk_pos.ne']
      rw [h3, div_le_one (mul_pos hp_pos hk_pos)]; nlinarith
    obtain ⟨x, y, xi, w₁, w₀, q, z₂, hx1, hx2, hy1, hy2, hxi0, hxi1,
      hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22, hmin_lt⟩ :=
      hcert δ d_r ⟨hδ_lo, hδ_hi⟩ ⟨hdr_lo, hdr_hi⟩
    set pref : ℝ := p * (ρ + d_r)
    set suf : ℝ := p * (1 + δ) - pref
    set U : ℝ := crossEntropy ρ pref x + crossEntropy len suf y
    set N : ℝ := U + crossEntropy suf (xi * len / 2) w₁ +
      crossEntropy (len - suf) (xi * len / 2) w₀ +
      max 0 (ρ + d_r - 508 / 1000) + 1 / 10 ^ 7
    set F : ℝ := 2 * crossEntropy ρ pref x + xi * len +
      crossEntropy (len - xi * len) (suf - xi * len / 2) q
    set M₂ : ℝ := crossEntropy (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂
    set u : ℝ := (r : ℝ) - ρ * (k : ℝ)
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u < 1 := by dsimp [u]; linarith
    have hsr_exact : (sr : ℝ) = pref * (k : ℝ) + p * u := by
      dsimp [pref, d_r, u]; field_simp [hp_pos.ne', hk_pos.ne']; ring
    have hL_exact : (L : ℝ) = len * (k : ℝ) - u := by
      have hcast : (L : ℝ) = (k : ℝ) - (r : ℝ) := Nat.cast_sub hrk
      dsimp [len, u]; rw [hcast]; ring
    have hj_exact : (j : ℝ) = suf * (k : ℝ) - p * u := by
      have hcast : (j : ℝ) = (s : ℝ) - (sr : ℝ) := Nat.cast_sub hsr_le_s
      have hs_ex : (s : ℝ) = p * (1 + δ) * (k : ℝ) := by
        dsimp [δ]; field_simp [hp_pos.ne', hk_pos.ne']; ring
      rw [hcast, hs_ex, hsr_exact]; dsimp [suf]; ring
    have hce_scale : ∀ (a' j' z' : ℝ), crossEntropy (a' * (k : ℝ)) (j' * (k : ℝ)) z' =
        crossEntropy a' j' z' * (k : ℝ) := fun a' j' z' => by unfold crossEntropy; ring
    have hce_pref_le : ∀ (z' : ℝ), (1 : ℝ) / 1024 ≤ z' → z' ≤ 1023 / 1024 →
        crossEntropy (r : ℝ) (sr : ℝ) z' ≤ crossEntropy ρ pref z' * (k : ℝ) + 10 := by
      intro z' hz1' hz2'
      have hlog := neg_logb2_le_ten hz1' hz2'
      rw [show (r : ℝ) = ρ * (k : ℝ) + u by dsimp [u]; ring, hsr_exact, ← hce_scale]
      unfold crossEntropy
      have hdiff : (pref * (k : ℝ) + p * u) * -Real.logb 2 z' +
          (ρ * (k : ℝ) + u - (pref * (k : ℝ) + p * u)) * -Real.logb 2 (1 - z') -
          (pref * (k : ℝ) * -Real.logb 2 z' + (ρ * (k : ℝ) - pref * (k : ℝ)) * -Real.logb 2 (1 - z')) =
          u * (p * (-Real.logb 2 z') + (1 - p) * (-Real.logb 2 (1 - z'))) := by ring
      have h1a := mul_le_mul_of_nonneg_left hlog.1 hp_pos.le
      have h1b := mul_le_mul_of_nonneg_left hlog.2 h1p_pos.le
      have h1 : p * (-Real.logb 2 z') + (1 - p) * (-Real.logb 2 (1 - z')) ≤ 10 := by linarith [h1a, h1b]
      have h2 : u * (p * (-Real.logb 2 z') + (1 - p) * (-Real.logb 2 (1 - z'))) ≤ u * 10 :=
        mul_le_mul_of_nonneg_left h1 hu0
      linarith [hdiff, h2, hu1]
    have hce_suf_le : ∀ (z' : ℝ), (1 : ℝ) / 1024 ≤ z' → z' ≤ 1023 / 1024 →
        crossEntropy (L : ℝ) (j : ℝ) z' ≤ crossEntropy len suf z' * (k : ℝ) := by
      intro z' hz1' hz2'
      have hnl1 : 0 ≤ -Real.logb 2 z' := by
        have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith : (0 : ℝ) ≤ z') (by linarith : z' ≤ 1); linarith
      have hnl2 : 0 ≤ -Real.logb 2 (1 - z') := by
        have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) (by linarith : (0 : ℝ) ≤ 1 - z') (by linarith : 1 - z' ≤ 1); linarith
      rw [hL_exact, hj_exact, ← hce_scale]
      unfold crossEntropy
      have hdiff : (suf * (k : ℝ) - p * u) * -Real.logb 2 z' +
          (len * (k : ℝ) - u - (suf * (k : ℝ) - p * u)) * -Real.logb 2 (1 - z') -
          (suf * (k : ℝ) * -Real.logb 2 z' + (len * (k : ℝ) - suf * (k : ℝ)) * -Real.logb 2 (1 - z')) =
          -(u * (p * (-Real.logb 2 z') + (1 - p) * (-Real.logb 2 (1 - z')))) := by ring
      have hnn : 0 ≤ u * (p * (-Real.logb 2 z') + (1 - p) * (-Real.logb 2 (1 - z'))) :=
        mul_nonneg hu0 (add_nonneg (mul_nonneg hp_pos.le hnl1) (mul_nonneg h1p_pos.le hnl2))
      linarith [hdiff, hnn]
    have hA_direct : (A.card : ℝ) ≤ (2 : ℝ) ^ (U * (k : ℝ) + 10) := by
      have hAsub_ps : A ⊆ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => oddCount r n = sr ∧ suffixOddCount r (k - r) n = j) := by
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hnS := (Finset.mem_filter.mp hn'.1).1
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnS).1, hn'.2.2, ?_⟩
        have hadd := oddCount_add r (k - r) n
        rw [Nat.add_sub_of_le hrk, hn'.2.1, hn'.2.2] at hadd
        unfold suffixOddCount; omega
      have h1 := le_trans (Nat.cast_le.mpr (Finset.card_le_card hAsub_ps))
        (card_shell_prefix_suffix_slice_le_rpow (x := x) (y := y) hrk hsr_le_r hjL
          (by linarith) (by linarith) (by linarith) (by linarith))
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
      have hx := hce_pref_le x hx1 hx2
      have hy := hce_suf_le y hy1 hy2
      dsimp [U, L] at hx hy ⊢; linarith
    rcases min_lt_iff.mp hmin_lt with hU_lt | hColl_lt
    · calc (A.card : ℝ) ≤ (2 : ℝ) ^ (U * (k : ℝ) + 10) := hA_direct
        _ = (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (U * (k : ℝ)) := by
            rw [add_comm, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ)) := by
            have h1 : (2 : ℝ) ^ (10 : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) := by
              have h10_30 : (2 : ℝ) ^ (10 : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              exact h10_30.trans (le_mul_of_one_le_right (by positivity) (by linarith [hk_pos]))
            have h2 : (2 : ℝ) ^ (U * (k : ℝ)) ≤ (2 : ℝ) ^ (v * (k : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hU_lt.le hk_pos.le)
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
    · have hNM_lt : (N + M₂) / 2 < v := (max_lt_iff.mp hColl_lt).1
      have hFM_lt : (F + M₂) / 2 < v := (max_lt_iff.mp hColl_lt).2
      have hAsub_S : A ⊆ twoWindowSurvivors k := fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have hAs : ∀ n ∈ A, oddCount k n = s := fun n hn => (Finset.mem_filter.mp hn).2.1
      have hAsr : ∀ n ∈ A, oddCount r n = sr := fun n hn => (Finset.mem_filter.mp hn).2.2
      have hAj : ∀ n ∈ A, suffixOddCount r L n = j := by
        intro n hn; have hn' := Finset.mem_filter.mp hn
        have hadd := oddCount_add r L n; rw [hrL, hn'.2.1, hn'.2.2] at hadd; unfold suffixOddCount; omega
      have hj_le_sk : (j : ℝ) ≤ suf * (k : ℝ) := by
        have hpu : 0 ≤ p * u := mul_nonneg hp_pos.le hu0
        linarith only [hj_exact, hpu]
      have hLj_le_sk : ((L - j : ℕ) : ℝ) ≤ (len - suf) * (k : ℝ) := by
        have hsub : ((L - j : ℕ) : ℝ) = (L : ℝ) - (j : ℝ) := Nat.cast_sub hjL
        have h1pu : 0 ≤ (1 - p) * u := mul_nonneg h1p_pos.le hu0
        linarith only [hsub, hL_exact, hj_exact, h1pu]
      exact good_shell_slice_collision_branch hk hrL rfl hsk hsr_le_r hjL h3lo h3hi hsep hAsub_S
        hAs hAsr hAj hA_direct hx1 hx2 hxi0 hxi1 hw11 hw12 hw01 hw02 hwsum hq1 hq2 hz21 hz22
        rfl rfl rfl (by linarith only [hL_exact, hu1]) (by linarith only [hL_exact, hu0])
        hj_le_sk hLj_le_sk
        rfl (hce_pref_le x hx1 hx2) (hce_suf_le q hq1 hq2) rfl rfl rfl hNM_lt hFM_lt
  · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
    positivity

/-- **Unified Good-Shell Slice-to-Shell Assembly Theorem:**
On any shell `k ≥ 2^{40}` satisfying `HasWrapSeparation σ k`, any uniform slice-exponent bound
`< v` (with tilts in `[1/1024, 1023/1024]` and `v + 4 / 10^9 ≤ a`) yields the constant-`1`
shell bound `((twoWindowSurvivors k).card : ℝ) ≤ 2^(a * k)` (and hence
`(shellNeverDrops k : ℝ) ≤ 2^(a * k)`). Works identically for both wide (`0.945`) and tight (`0.94476`)! -/
theorem good_shell_twoWindowSurvivors_le {σ v a : ℝ} {k : ℕ}
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 10 ^ 4)
    (hv_ge : 943928 / 10 ^ 6 ≤ v)
    (hva : v + 4 / 10 ^ 9 ≤ a)
    (hk : 2 ^ 40 ≤ k)
    (hsep : HasWrapSeparation σ k)
    (hcert : ∀ δ d_r : ℝ,
      -(1 / 10 ^ 7 : ℝ) ≤ δ ∧ δ ≤ 12 / 1000 →
      -(1 / 10 ^ 7 : ℝ) ≤ d_r ∧ d_r ≤ 1 →
      let p := Real.log 2 / Real.log 3
      let rho := 492 / 1000 + δ + 3 / 10 ^ 7 + σ
      let len := 1 - rho
      let pref := p * (rho + d_r)
      let suf := p * (1 + δ) - pref
      ∃ x y xi w₁ w₀ q z₂ : ℝ,
        (1 : ℝ) / 1024 ≤ x ∧ x ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ y ∧ y ≤ 1023 / 1024 ∧
        0 < xi ∧ xi < 1 ∧
        (1 : ℝ) / 1024 ≤ w₁ ∧ w₁ ≤ 1023 / 1024 ∧
        (1 : ℝ) / 1024 ≤ w₀ ∧ w₀ ≤ 1023 / 1024 ∧ w₁ + w₀ ≤ 1 ∧
        (1 : ℝ) / 1024 ≤ q ∧ q ≤ 1023 / 1024 ∧
        (1 : ℝ) / 2 ≤ z₂ ∧ z₂ ≤ 1023 / 1024 ∧
        let U := crossEntropy rho pref x + crossEntropy len suf y
        let N := U + crossEntropy suf (xi * len / 2) w₁ +
          crossEntropy (len - suf) (xi * len / 2) w₀ +
          max 0 (rho + d_r - 508 / 1000) + 1 / 10 ^ 7
        let F := 2 * crossEntropy rho pref x + xi * len +
          crossEntropy (len - xi * len) (suf - xi * len / 2) q
        let M₂ := crossEntropy (508 / 1000) (p * (508 / 1000 - δ - (1 / 10 ^ 7) * (1508 / 1000))) z₂
        min U (max ((N + M₂) / 2) ((F + M₂) / 2)) < v) :
    ((twoWindowSurvivors k).card : ℝ) ≤ (2 : ℝ) ^ (a * (k : ℝ)) := by
  classical
  set p : ℝ := Real.log 2 / Real.log 3
  have hk_r := cast_ge_two_pow_40 hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hp_pos : 0 < p := by have := log3_two_bounds.1; linarith
  set Tail := (twoWindowSurvivors k).filter
    (fun n => (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ oddCount k n)
  set Mid := (twoWindowSurvivors k).filter
    (fun n => (3 : ℝ) ^ oddCount k n < (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)))
  have hsplit_card : (twoWindowSurvivors k).card = Tail.card + Mid.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext n; simp only [Tail, Mid, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hn; by_cases h : (2 : ℝ) ^ ((1012 / 1000 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ oddCount k n
        · exact Or.inl ⟨hn, h⟩
        · exact Or.inr ⟨hn, lt_of_not_ge h⟩
      · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
    · rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Tail, Mid, Finset.mem_filter] at h1 h2; linarith
  have hTail : (Tail.card : ℝ) ≤ (2 : ℝ) ^ (v * (k : ℝ)) :=
    (high_product_tail_card_le k).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hv_ge hk_pos.le))
  let rOf (s : ℕ) : ℕ :=
    Nat.ceil ((492 / 1000 + ((s : ℝ) / (p * (k : ℝ)) - 1) + 3 / 10 ^ 7 + σ) * (k : ℝ))
  let Slice (s sr : ℕ) : Finset ℕ :=
    Mid.filter (fun n => oddCount k n = s ∧ oddCount (rOf s) n = sr)
  have hMid_cov : Mid ⊆ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).biUnion (fun ps => Slice ps.1 ps.2) := by
    intro n hn
    have hsk : oddCount k n ≤ k := oddCount_le k n
    have hnM := Finset.mem_filter.mp hn
    have h3lo := (Finset.mem_filter.mp hnM.1).2 k (Nat.le_add_right k _)
    have hδ_hi : ((oddCount k n : ℝ) / (p * (k : ℝ)) - 1) < 12 / 1000 := by
      have hlt := oddCount_lt_of_three_pow_lt_rpow hnM.2
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (mul_pos hp_pos hk_pos)]; dsimp [p] at hlt ⊢; linarith
    have hrk : rOf (oddCount k n) ≤ k := by
      have : (rOf (oddCount k n) : ℝ) ≤ (k : ℝ) := by
        dsimp [rOf]
        have hδ_lo : -(1 / 10 ^ 7 : ℝ) ≤ (oddCount k n : ℝ) / (p * (k : ℝ)) - 1 := by
          have hge := oddCount_ge_of_rpow_le_three_pow h3lo
          rw [le_sub_iff_add_le, le_div_iff₀ (mul_pos hp_pos hk_pos)]; dsimp [p] at hge ⊢; linarith
        have hnn : 0 ≤ (492 / 1000 + ((oddCount k n : ℝ) / (p * (k : ℝ)) - 1) + 3 / 10 ^ 7 + σ) * (k : ℝ) := by
          nlinarith
        have hlt := Nat.ceil_lt_add_one hnn
        nlinarith
      exact_mod_cast this
    have hsrk : oddCount (rOf (oddCount k n)) n ≤ k := (oddCount_le _ n).trans hrk
    refine Finset.mem_biUnion.mpr ⟨(oddCount k n, oddCount (rOf (oddCount k n)) n),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hsk),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hsrk)⟩,
      Finset.mem_filter.mpr ⟨hn, rfl, rfl⟩⟩
  have hSlice_bound : ∀ ps ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1),
      ((Slice ps.1 ps.2).card : ℝ) ≤ (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ)) :=
    fun ps _ => good_shell_single_slice_le hσ hk hsep hcert
  have hMid_le : (Mid.card : ℝ) ≤
      (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (v * (k : ℝ)) := by
    have hnat : Mid.card ≤ ∑ ps ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1), (Slice ps.1 ps.2).card :=
      (Finset.card_le_card hMid_cov).trans Finset.card_biUnion_le
    calc (Mid.card : ℝ)
        ≤ ∑ ps ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1), ((Slice ps.1 ps.2).card : ℝ) := by
          exact_mod_cast hnat
      _ ≤ ∑ _ps ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1),
            ((2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ))) :=
          Finset.sum_le_sum hSlice_bound
      _ = (((Finset.range (k + 1) ×ˢ Finset.range (k + 1)).card : ℕ) : ℝ) *
            ((2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ (v * (k : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 : ℝ) ^ (30 : ℝ) * ((k : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (v * (k : ℝ)) := by
          rw [Finset.card_product, Finset.card_range]; push_cast; ring
  have hTotal : ((twoWindowSurvivors k).card : ℝ) ≤
      (2 : ℝ) ^ (65 : ℝ) * ((k : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (v * (k : ℝ)) := by
    have hcast : ((twoWindowSurvivors k).card : ℝ) = (Tail.card : ℝ) + (Mid.card : ℝ) := by
      exact_mod_cast hsplit_card
    have h1_le : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [hk_pos])
    have h2_le : (1 : ℝ) + (2 : ℝ) ^ (30 : ℝ) ≤ (2 : ℝ) ^ (65 : ℝ) := by norm_num
    nlinarith [hcast, hTail, hMid_le, h1_le, h2_le, show (0 : ℝ) ≤ (2 : ℝ) ^ (v * (k : ℝ)) by positivity]
  have hAbsorb : (2 : ℝ) ^ (65 : ℝ) * ((k : ℝ) + 1) ^ 3 ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) := by
    have hpa := prefactor_absorption_ge_two_pow_40 hk
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hlhs_eq : (2 : ℝ) ^ (65 : ℝ) * ((k : ℝ) + 1) ^ 3 =
        (2 : ℝ) ^ (65 + 3 * Real.logb 2 ((k : ℝ) + 1)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm 3,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hk1_pos,
        show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
    rw [hlhs_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hpa.le
  calc ((twoWindowSurvivors k).card : ℝ)
      ≤ (2 : ℝ) ^ (65 : ℝ) * ((k : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (v * (k : ℝ)) := hTotal
    _ ≤ (2 : ℝ) ^ ((4 / 10 ^ 9 : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (v * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hAbsorb (by positivity)
    _ = (2 : ℝ) ^ ((v + 4 / 10 ^ 9) * (k : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    _ ≤ (2 : ℝ) ^ (a * (k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hva hk_pos.le)

/-! ## 3. End-to-End Pure-Kernel Master Theorems (`0.945` Wide & `0.94476` Tight) -/

/-- **End-to-End Wide-Slack `ShellSeparationCovering` Construction (`a = 0.945`, `σ = 10^{-4}`):**
Parameterized SOLELY by `ThreePlaceSubspaceHypothesis` (zero extra analytic assumptions!). -/
theorem collatz_two_window_wide_0945_covering {H₀ : ℝ} {R : ℕ}
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hsub : ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R) :
    ∃ cov : ShellSeparationCovering,
      cov.a = 945 / 1000 ∧ cov.b = 94995558 / 10 ^ 8 ∧ cov.ρ_band = 3041 / 1000 ∧
      cov.K = 2 ^ 40 ∧ cov.R = R := by
  have hbands := subspace_implies_exceptional_bands
    (c_lo := 49597 / 100000) (c_hi := 150801 / 100000) (k_star := 2 ^ 40)
    (by norm_num) hsub (fun k => ¬ HasWrapSeparation (1 / 10 ^ 4) k)
    (fun k hk hfail => by
      have h := wrap_separation_failure_witness (Or.inl rfl) hH₀ hk hfail
      have heq : ((1 : ℝ) / 10 ^ 4) / 2 = 1 / 20000 := by norm_num
      rwa [heq] at h)
  obtain ⟨K_left, hK_ge, hK_cov⟩ := hbands
  have hratio_lt : (150801 / 100000 : ℝ) / (49597 / 100000 : ℝ) ≤ 3041 / 1000 := by norm_num
  have h24 : 24 ≤ 2 ^ 40 := by norm_num
  refine ⟨{
    a := 945 / 1000
    b := 94995558 / 10 ^ 8
    ρ_band := 3041 / 1000
    K := 2 ^ 40
    R := R
    leftEnds := K_left
    ha_gt := by norm_num
    hab := by norm_num
    hb_lt := by norm_num
    hρ_nonneg := by norm_num
    hK := by norm_num
    hleft_ge := hK_ge
    hall := fun k hk => all_shell_neverDrops_le (le_trans h24 hk)
    hgood := fun k hk hnotbad => by
      have hsep : HasWrapSeparation (1 / 10 ^ 4) k := by
        by_contra hfail
        obtain ⟨i, hi1, hi2⟩ := hK_cov k hk hfail
        exact hnotbad i ⟨hi1, hi2.trans (mul_le_mul_of_nonneg_right hratio_lt (Nat.cast_nonneg _))⟩
      have hS := good_shell_twoWindowSurvivors_le (σ := 1 / 10 ^ 4) (v := 9449 / 10000)
        (a := 945 / 1000) ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num) hk hsep
        (fun δ d_r hδ hd_r => by
          obtain ⟨x, y, xi, w₁, w₀, q, z₂, hx1, hx2, hy1, hy2, hxi1, hxi2,
            hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22, hlt⟩ :=
            wide_slack_0055_uniform_bound_with_floor δ d_r hδ hd_r
          refine ⟨x, y, xi, w₁, w₀, q, z₂,
            by linarith, by linarith, by linarith, by linarith,
            by linarith, by linarith, by linarith, by linarith,
            by linarith, by linarith, hwsum, by linarith, by linarith,
            hz21, by linarith, ?_⟩
          have hrho_eq : (492 / 1000 : ℝ) + δ + 3 / 10 ^ 7 + 1 / 10 ^ 4 = wideRho δ := by
            unfold wideRho; ring
          unfold wideDirect wideNear wideFar wideMenu wideLen widePref wideSuf at hlt
          rw [← hrho_eq] at hlt
          exact hlt)
      exact (Nat.cast_le.mpr (shellNeverDrops_le_twoWindowSurvivors (le_trans h24 hk))).trans hS
  }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **End-to-End Pure-Kernel Wide-Slack `0.945` Master Theorem (Theorems 1(a) & 3):**
Parameterized SOLELY by `ThreePlaceSubspaceHypothesis (1 / 20000) H₀ R` (satisfied by
Evertse–Ferretti 2013 with `H₀ = 2^{80,000}`, `R ≤ 10^{43}` and Schlickewei 1990/1992 with
`H₀ = 2^{160,000}`), deduces unconditionally in Lean 4:
(i) `shellNeverDrops k ≤ 2^{0.945 k}` outside `R` bands `[K_i, 3.041 K_i]` (+ all-shell `2^{0.94995558 k}`),
(ii) `N_T X ≤ 5 X^{0.945}` for all `X ≥ 2^{2 * 2^{40}}` outside `[2^{K_i}, (2^{K_i})^{3.06}]`,
(iii) every `[X₁, X₁^{3.2^{R+1}}]` (`X₁ ≥ 2^{2 * 2^{40}}`) contains an integer `x` with `N_T x ≤ 5 x^{0.945}`,
(iv) eventual `∃ C > 0, ∀ X ≥ 1, N_T X ≤ C X^{0.945}`. -/
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
  obtain ⟨cov, ha, hb, hρ, hK, hR⟩ := collatz_two_window_wide_0945_covering hH₀ hsub
  have hband : cov.ρ_band * cov.b ≤ ((306 : ℝ) / 100) * cov.a := by
    rw [hρ, hb, ha]; norm_num
  refine ⟨fun i => cov.leftEnds (Fin.cast hR.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [← hK]; exact cov.hleft_ge _
  · intro k hk hnot
    have := cov.hgood k (by rwa [hK]) (fun j => by
      have h := hnot (Fin.cast hR j)
      simpa [hρ] using h)
    rwa [ha] at this
  · intro X hX hXout
    have := cumulative_count_outside_bands cov hband X (by rwa [hK]) (fun j => by
      have h := hXout (Fin.cast hR j); simpa using h)
    rwa [ha] at this
  · intro X₁ hX₁
    have hX₁_ge10 : (2 : ℝ) ^ 10 ≤ X₁ := by
      have hpow : (2 : ℝ) ^ 10 ≤ ((2 ^ (2 * 2 ^ 40) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 10 ≤ 2 * 2 ^ 40)
      exact hpow.trans hX₁
    obtain ⟨x, hx1, hx2, hxout⟩ := good_scale_in_window cov.R
      (fun j => (2 : ℝ) ^ (cov.leftEnds j))
      (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) X₁ hX₁_ge10
    have hx_ge : 2 ^ (2 * cov.K) ≤ x := by
      rw [hK]
      exact Nat.cast_le.mp (hX₁.trans hx1)
    have hN := cumulative_count_outside_bands cov hband x hx_ge hxout
    rw [ha] at hN; rw [hR] at hx2
    exact ⟨x, hx1, hx2, hN⟩
  · have := eventual_bound_of_shell_covering cov
    rwa [ha] at this

/-- **End-to-End Tight-Slack `ShellSeparationCovering` Construction (`a = 0.94476`, `σ = 10^{-7}`):**
Uses our pure-kernel 401-leaf `tight_slack_005524_uniform_bound` (`< 944759996 / 10^9`) and
is parameterized SOLELY by `ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R`. -/
theorem collatz_two_window_tight_094476_covering {H₀ : ℝ} {R : ℕ}
    (hH₀ : H₀ ≤ (2 : ℝ) ^ ((49597 / 100000 : ℝ) * ((2 ^ 40 : ℕ) : ℝ)))
    (hsub : ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R) :
    ∃ cov : ShellSeparationCovering,
      cov.a = 94476 / 10 ^ 5 ∧ cov.b = 94995558 / 10 ^ 8 ∧ cov.ρ_band = 3041 / 1000 ∧
      cov.K = 2 ^ 40 ∧ cov.R = R := by
  have hbands := subspace_implies_exceptional_bands
    (c_lo := 49597 / 100000) (c_hi := 150801 / 100000) (k_star := 2 ^ 40)
    (by norm_num) hsub (fun k => ¬ HasWrapSeparation (1 / 10 ^ 7) k)
    (fun k hk hfail => by
      have h := wrap_separation_failure_witness (Or.inr rfl) hH₀ hk hfail
      have heq : ((1 : ℝ) / 10 ^ 7) / 2 = 1 / 20000000 := by norm_num
      rwa [heq] at h)
  obtain ⟨K_left, hK_ge, hK_cov⟩ := hbands
  have hratio_lt : (150801 / 100000 : ℝ) / (49597 / 100000 : ℝ) ≤ 3041 / 1000 := by norm_num
  have h24 : 24 ≤ 2 ^ 40 := by norm_num
  refine ⟨{
    a := 94476 / 10 ^ 5
    b := 94995558 / 10 ^ 8
    ρ_band := 3041 / 1000
    K := 2 ^ 40
    R := R
    leftEnds := K_left
    ha_gt := by norm_num
    hab := by norm_num
    hb_lt := by norm_num
    hρ_nonneg := by norm_num
    hK := by norm_num
    hleft_ge := hK_ge
    hall := fun k hk => all_shell_neverDrops_le (le_trans h24 hk)
    hgood := fun k hk hnotbad => by
      have hsep : HasWrapSeparation (1 / 10 ^ 7) k := by
        by_contra hfail
        obtain ⟨i, hi1, hi2⟩ := hK_cov k hk hfail
        exact hnotbad i ⟨hi1, hi2.trans (mul_le_mul_of_nonneg_right hratio_lt (Nat.cast_nonneg _))⟩
      have hS := good_shell_twoWindowSurvivors_le (σ := 1 / 10 ^ 7) (v := 944759996 / 10 ^ 9)
        (a := 94476 / 10 ^ 5) ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num) hk hsep
        (fun δ d_r hδ hd_r => by
          obtain ⟨x, y, xi, w₁, w₀, q, z₂, hx1, hx2, hy1, hy2, hxi1, hxi2,
            hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22, hlt⟩ :=
            tight_slack_005524_uniform_bound δ d_r hδ hd_r
          refine ⟨x, y, xi, w₁, w₀, q, z₂,
            hx1, hx2, hy1, hy2, by linarith, by linarith,
            hw11, hw12, hw01, hw02, hwsum, hq1, hq2, hz21, hz22, ?_⟩
          have hrho_eq : (492 / 1000 : ℝ) + δ + 3 / 10 ^ 7 + 1 / 10 ^ 7 = tightRho δ := by
            unfold tightRho; ring
          unfold tightNear tightFar tightDirect tightMenu tightLen tightSuf tightPref at hlt
          rw [← hrho_eq] at hlt
          dsimp only
          exact hlt)
      exact (Nat.cast_le.mpr (shellNeverDrops_le_twoWindowSurvivors (le_trans h24 hk))).trans hS
  }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **End-to-End Pure-Kernel Tight-Slack `0.94476` Master Theorem (Theorems 1(b) & 3):**
Parameterized SOLELY by `ThreePlaceSubspaceHypothesis (1 / 20000000) H₀ R` (satisfied by
Evertse–Ferretti 2013 with `H₀ = 2^{80,000,000}`, `R ≤ 10^{58}` and Schlickewei 1990/1992 with
`H₀ = 2^{160,000,000}`), deduces unconditionally in pure-kernel Lean 4 all four conclusions of
Theorems 1(b) and 3 at the headline exponent **`a = 0.94476`**. -/
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
  obtain ⟨cov, ha, hb, hρ, hK, hR⟩ := collatz_two_window_tight_094476_covering hH₀ hsub
  have hband : cov.ρ_band * cov.b ≤ ((306 : ℝ) / 100) * cov.a := by
    rw [hρ, hb, ha]; norm_num
  refine ⟨fun i => cov.leftEnds (Fin.cast hR.symm i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [← hK]; exact cov.hleft_ge _
  · intro k hk hnot
    have := cov.hgood k (by rwa [hK]) (fun j => by
      have h := hnot (Fin.cast hR j)
      simpa [hρ] using h)
    rwa [ha] at this
  · intro X hX hXout
    have := cumulative_count_outside_bands cov hband X (by rwa [hK]) (fun j => by
      have h := hXout (Fin.cast hR j); simpa using h)
    rwa [ha] at this
  · intro X₁ hX₁
    have hX₁_ge10 : (2 : ℝ) ^ 10 ≤ X₁ := by
      have hpow : (2 : ℝ) ^ 10 ≤ ((2 ^ (2 * 2 ^ 40) : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 10 ≤ 2 * 2 ^ 40)
      exact hpow.trans hX₁
    obtain ⟨x, hx1, hx2, hxout⟩ := good_scale_in_window cov.R
      (fun j => (2 : ℝ) ^ (cov.leftEnds j))
      (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) X₁ hX₁_ge10
    have hx_ge : 2 ^ (2 * cov.K) ≤ x := by
      rw [hK]
      exact Nat.cast_le.mp (hX₁.trans hx1)
    have hN := cumulative_count_outside_bands cov hband x hx_ge hxout
    rw [ha] at hN; rw [hR] at hx2
    exact ⟨x, hx1, hx2, hN⟩
  · have := eventual_bound_of_shell_covering cov
    rwa [ha] at this

/-! ## 4. Structural Obstructions, Terras (1976/1979), & Scholar-Verified Comparisons -/

/-- **Lagarias (1985, Sec. 2.5) 3-Step Coalescence (`8t + 4` & `8t + 5`):**
Both `8t + 4` (parity word EEO) and `8t + 5` (parity word OEE) map in 3 shortcut steps to
`3t + 2` with exactly 1 odd step, showing why naive shift-1 coupling collapses. -/
theorem coalescence_8k_plus_4_5 (t : ℕ) :
    T^[3] (8 * t + 4) = 3 * t + 2 ∧
    T^[3] (8 * t + 5) = 3 * t + 2 ∧
    oddCount 3 (8 * t + 4) = 1 ∧
    oddCount 3 (8 * t + 5) = 1 := by
  have h1a : T (8 * t + 4) = 4 * t + 2 := by rw [T_even (by omega)]; omega
  have h2a : T (4 * t + 2) = 2 * t + 1 := by rw [T_even (by omega)]; omega
  have h3a : T (2 * t + 1) = 3 * t + 2 := by rw [T_odd (by omega)]; omega
  have h1b : T (8 * t + 5) = 12 * t + 8 := by rw [T_odd (by omega)]; omega
  have h2b : T (12 * t + 8) = 6 * t + 4 := by rw [T_even (by omega)]; omega
  have h3b : T (6 * t + 4) = 3 * t + 2 := by rw [T_even (by omega)]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change T (T (T (8 * t + 4))) = 3 * t + 2; rw [h1a, h2a, h3a]
  · change T (T (T (8 * t + 5))) = 3 * t + 2; rw [h1b, h2b, h3b]
  · have hm1 : (8 * t + 4) % 2 = 0 := by omega
    have hm2 : (4 * t + 2) % 2 = 0 := by omega
    have hm3 : (2 * t + 1) % 2 = 1 := by omega
    simp [oddCount, h1a, h2a, hm1, hm2, hm3]
  · have hm1 : (8 * t + 5) % 2 = 1 := by omega
    have hm2 : (12 * t + 8) % 2 = 0 := by omega
    have hm3 : (6 * t + 4) % 2 = 0 := by omega
    simp [oddCount, h1b, h2b, hm1, hm2, hm3]

/-- **Shift-1 Tilted Autocorrelation Lower Bound (Proposition 4(b)):**
For every `k ≥ 3` and `u ≥ 0`,
`u * (1 + u)^(k - 3) ≤ ∑_{n < 2^k} √(u^{s_k(n)} * u^{s_k(n + 1)})`. -/
theorem shift_one_autocorrelation_lower {k : ℕ} (hk : 3 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    u * (1 + u) ^ (k - 3) ≤
      ∑ n ∈ Finset.range (2 ^ k),
        Real.sqrt (u ^ oddCount k n * u ^ oddCount k (n + 1)) := by
  set m := k - 3
  have hm3 : 3 + m = k := by omega
  -- Restrict to the 2^m coalescing starts n = 8 * t + 4 for t < 2^m:
  set S : Finset ℕ := (Finset.range (2 ^ m)).image (fun t => 8 * t + 4)
  have hSsub : S ⊆ Finset.range (2 ^ k) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rw [Finset.mem_range] at ht ⊢
    have hpow : 2 ^ k = 8 * 2 ^ m := by rw [← hm3, pow_add]; norm_num
    omega
  have hle : ∑ n ∈ S, Real.sqrt (u ^ oddCount k n * u ^ oddCount k (n + 1)) ≤
      ∑ n ∈ Finset.range (2 ^ k), Real.sqrt (u ^ oddCount k n * u ^ oddCount k (n + 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => Real.sqrt_nonneg _)
  have hinj : Set.InjOn (fun t : ℕ => 8 * t + 4) (Finset.range (2 ^ m) : Set ℕ) := by
    intro t₁ _ t₂ _ h; dsimp only at h; omega
  rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)] at hle
  -- On each n = 8*t + 4, oddCount k (8t+4) = oddCount k (8t+5) = 1 + oddCount m (3t+2):
  have hterm : ∀ t ∈ Finset.range (2 ^ m),
      Real.sqrt (u ^ oddCount k (8 * t + 4) * u ^ oddCount k (8 * t + 4 + 1)) =
        u * u ^ oddCount m ((3 * t + 2) % 2 ^ m) := by
    intro t _
    obtain ⟨hT1, hT2, ho1, ho2⟩ := coalescence_8k_plus_4_5 t
    have hc1 : oddCount k (8 * t + 4) = 1 + oddCount m (3 * t + 2) := by
      rw [← hm3, oddCount_add, hT1, ho1]
    have hc2 : oddCount k (8 * t + 4 + 1) = 1 + oddCount m (3 * t + 2) := by
      rw [show 8 * t + 4 + 1 = 8 * t + 5 by omega, ← hm3, oddCount_add, hT2, ho2]
    rw [hc1, hc2, Real.sqrt_mul_self (pow_nonneg hu _), pow_add, pow_one, oddCount_mod]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hle
  -- t ↦ (3*t + 2) % 2^m is a bijection on range (2^m) since gcd(3, 2^m) = 1!
  have hperm :
      ∑ t ∈ Finset.range (2 ^ m), u ^ oddCount m ((3 * t + 2) % 2 ^ m) =
        ∑ r ∈ Finset.range (2 ^ m), u ^ oddCount m r := by
    have hcop : Nat.Coprime 3 (2 ^ m) := (by decide : Nat.Coprime 3 2).pow_right m
    have hbij : Set.BijOn (fun t => (3 * t + 2) % 2 ^ m)
        (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) := by
      refine ⟨fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_, ?_⟩
      · intro t₁ ht₁ t₂ ht₂ heq
        have hm : 3 * t₁ + 2 ≡ 3 * t₂ + 2 [MOD 2 ^ m] := heq
        have h3 : 3 * t₁ ≡ 3 * t₂ [MOD 2 ^ m] := Nat.ModEq.add_right_cancel' 2 hm
        have h1 : t₁ ≡ t₂ [MOD 2 ^ m] := Nat.ModEq.cancel_left_of_coprime hcop.symm h3
        change t₁ % 2 ^ m = t₂ % 2 ^ m at h1
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp ht₁),
          Nat.mod_eq_of_lt (Finset.mem_range.mp ht₂)] at h1
        exact h1
      · intro y hy
        -- Finite injective map from Finset.range (2^m) to itself is surjective!
        have hmaps : (Finset.range (2 ^ m)).image (fun t => (3 * t + 2) % 2 ^ m) = Finset.range (2 ^ m) := by
          apply Finset.eq_of_subset_of_card_le
          · intro z hz; rcases Finset.mem_image.mp hz with ⟨t, _, rfl⟩
            exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
          · rw [Finset.card_image_of_injOn]
            intro t₁ ht₁ t₂ ht₂ heq
            have hm : 3 * t₁ + 2 ≡ 3 * t₂ + 2 [MOD 2 ^ m] := heq
            have h3 : 3 * t₁ ≡ 3 * t₂ [MOD 2 ^ m] := Nat.ModEq.add_right_cancel' 2 hm
            have h1 : t₁ ≡ t₂ [MOD 2 ^ m] := Nat.ModEq.cancel_left_of_coprime hcop.symm h3
            change t₁ % 2 ^ m = t₂ % 2 ^ m at h1
            rw [Nat.mod_eq_of_lt (Finset.mem_range.mp ht₁),
              Nat.mod_eq_of_lt (Finset.mem_range.mp ht₂)] at h1
            exact h1
        have hy' : y ∈ (Finset.range (2 ^ m)).image (fun t => (3 * t + 2) % 2 ^ m) := by rwa [hmaps]
        rcases Finset.mem_image.mp hy' with ⟨t, ht, rfl⟩
        exact ⟨t, ht, rfl⟩
    exact Finset.sum_bij (fun t _ => (3 * t + 2) % 2 ^ m)
      (fun t ht => hbij.1 ht) (fun t₁ ht₁ t₂ ht₂ h => hbij.2.1 ht₁ ht₂ h)
      (fun y hy => by rcases hbij.2.2 hy with ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
      (fun _ _ => rfl)
  -- Finally, ∑_{r < 2^m} u^(oddCount m r) = (1 + u)^m by tiltedMass_sum_eq_one!
  have hsum_eq : ∑ r ∈ Finset.range (2 ^ m), u ^ oddCount m r = (1 + u) ^ m := by
    have hpos : 0 < 1 + u := by linarith
    have htm := tiltedMass_sum_eq_one (u / (1 + u)) m
    have hterm_eq : ∀ r ∈ Finset.range (2 ^ m),
        tiltedMass (u / (1 + u)) m r = u ^ oddCount m r / (1 + u) ^ m := by
      intro r _
      unfold tiltedMass
      have h1 : 1 - u / (1 + u) = 1 / (1 + u) := by field_simp [hpos.ne']; ring
      rw [h1, div_pow, div_pow, one_pow, div_mul_div_comm, mul_one,
        ← pow_add, Nat.add_sub_of_le (oddCount_le m r)]
    rw [Finset.sum_congr rfl hterm_eq, ← Finset.sum_div, div_eq_one_iff_eq (pow_ne_zero m hpos.ne')] at htm
    exact htm
  rw [hperm, hsum_eq] at hle
  exact hle

/-- **Cauchy–Schwarz Self-Collision Floor (Proposition 4(c)):**
Every element collides with itself (`c_y^2 ≥ c_y`), so `|A| ≤ collisionCount A f`. -/
theorem collisionCount_ge_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    A.card ≤ collisionCount A f := by
  unfold collisionCount
  have hdiag : A.image (fun a => (a, a)) ⊆ (A ×ˢ A).filter (fun p => f p.1 = f p.2) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
  calc A.card = (A.image (fun a => (a, a))).card :=
        (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)).symm
    _ ≤ ((A ×ˢ A).filter (fun p => f p.1 = f p.2)).card := Finset.card_le_card hdiag

/-- Unrestricted Cauchy–Schwarz lower bound: for any nonempty menu `S`, `√|A| ≤ √(|S| * C(A, f))`. -/
theorem cauchy_schwarz_self_collision_floor {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (S : Finset β) (f : α → β) (hS : 1 ≤ S.card) :
    Real.sqrt (A.card : ℝ) ≤ Real.sqrt ((S.card : ℝ) * (collisionCount A f : ℝ)) := by
  apply Real.sqrt_le_sqrt
  have h1 : (A.card : ℝ) ≤ (collisionCount A f : ℝ) := by exact_mod_cast collisionCount_ge_card A f
  have h2 : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  nlinarith

/-- Half-entropy self-collision floor constant: `0.4749775 < H_2(log_3 2) / 2 < 0.474978`. -/
theorem lagarias_half_entropy_bounds :
    4749775 / 10 ^ 7 < binEntropy (Real.log 2 / Real.log 3) / 2 ∧
    binEntropy (Real.log 2 / Real.log 3) / 2 < 474978 / 10 ^ 6 := by
  have h := lagarias_entropy_bounds
  constructor <;> linarith

/-- Stopping-time predicate: `n` drops strictly below `n` within at most `k` shortcut steps. -/
def StopsWithin (k n : ℕ) : Prop :=
  ∃ j ∈ Finset.Icc 1 k, T^[j] n < n

instance (k n : ℕ) : Decidable (StopsWithin k n) := by
  unfold StopsWithin
  infer_instance

/-- **Terras (1979, pp. 101–102) Exact Finite-Additivity Stopping-Time Complementarity:**
For every `X ≥ 1` and horizon `k`, the densities of `{1 ≤ n ≤ X : χ(n) ≤ k}` and
`{1 ≤ n ≤ X : χ(n) > k}` sum identically to `1` without any infinite sum. -/
theorem terras_1979_finite_additivity (X k : ℕ) :
    let stopped := ((Finset.Icc 1 X).filter (fun n => StopsWithin k n)).card
    let surviving := ((Finset.Icc 1 X).filter (fun n => ¬ StopsWithin k n)).card
    stopped + surviving = X ∧
    (1 ≤ X → (stopped : ℝ) / (X : ℝ) + (surviving : ℝ) / (X : ℝ) = 1) := by
  classical
  intro stopped surviving
  have hsum : stopped + surviving = X := by
    dsimp [stopped, surviving]
    rw [← Finset.card_union_of_disjoint]
    · have hun : (Finset.Icc 1 X).filter (fun n => StopsWithin k n) ∪
          (Finset.Icc 1 X).filter (fun n => ¬ StopsWithin k n) = Finset.Icc 1 X := by
        ext n; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      rw [hun, Nat.card_Icc]; omega
    · rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact h2.2 h1.2
  refine ⟨hsum, fun hX => ?_⟩
  have hXr : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← add_div]
  have hcast : (stopped : ℝ) + (surviving : ℝ) = (X : ℝ) := by exact_mod_cast hsum
  rw [hcast, div_self hXr]

/-- Decidable Terras coefficient-stopping-time survivor check through horizon `m`:
`3^{s_i(n)} ≥ 2^i` for all `1 ≤ i ≤ m`. -/
def coeffSurvives (m n : ℕ) : Bool :=
  let rec go (i s x : ℕ) : Bool :=
    match i with
    | 0 => true
    | rem + 1 =>
        let stepIdx := m - rem
        let s' := if x % 2 = 1 then s + 1 else s
        let x' := if x % 2 = 1 then (3 * x + 1) / 2 else x / 2
        if 2 ^ stepIdx ≤ 3 ^ s' then go rem s' x' else false
  go m 0 n

/-- **Terras (1976, Table A, p. 247) & Paper 1 Table 3 Exact `k = 10` Shell Verification:**
In pure-kernel Lean 4 (`decide +kernel`):
- Terras `τ(n) ≥ 10` (`1 ≤ i ≤ 9`): exactly `76` of `1024` residues survive, giving
  `2 F(10) = 2 * 76 / 1024 = 19 / 128 = 0.1484375`.
- Paper 1 Table 3 `k = 10`: `|E_{10}| = 64` (10-step prefix survivors) and
  `S_{10} = 39` (15-step two-window survivors on `[2^{10}, 2^{11})`). -/
theorem terras_1976_tableA_and_shell_k10 :
    ((Finset.range 1024).filter (fun n => coeffSurvives 9 n)).card = 76 ∧
    ((2 * 76 : ℚ) / 1024 = 19 / 128) ∧
    ((Finset.range 1024).filter (fun n => coeffSurvives 10 n)).card = 64 ∧
    ((Finset.Ico 1024 2048).filter (fun n => coeffSurvives 15 n)).card = 39 := by
  decide +kernel

/-- **Finite-Residue Pigeonhole Principle (Proposition 4(a) Mechanism):**
Any finite set `A : Finset ℤ` with `2^r < A.card` contains two distinct elements congruent
modulo `2^r`, preventing wrap separation at that scale. -/
theorem pigeonhole_mod_two_pow {r : ℕ} {A : Finset ℤ} (hcard : 2 ^ r < A.card) :
    ∃ d₁ ∈ A, ∃ d₂ ∈ A, d₁ ≠ d₂ ∧ d₁ % (2 ^ r : ℤ) = d₂ % (2 ^ r : ℤ) := by
  have h2r_pos : (0 : ℤ) < (2 ^ r : ℤ) := by positivity
  set R : Finset ℤ := (Finset.range (2 ^ r)).image (fun n : ℕ => (n : ℤ))
  have hR_card : R.card = 2 ^ r := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hmaps : ∀ d ∈ A, d % (2 ^ r : ℤ) ∈ R := by
    intro d _
    have hnn : 0 ≤ d % (2 ^ r : ℤ) := Int.emod_nonneg d h2r_pos.ne'
    have hlt : d % (2 ^ r : ℤ) < (2 ^ r : ℤ) := Int.emod_lt_of_pos d h2r_pos
    refine Finset.mem_image.mpr ⟨(d % (2 ^ r : ℤ)).toNat, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hnn⟩
    have hcast : (((d % (2 ^ r : ℤ)).toNat : ℕ) : ℤ) < ((2 ^ r : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; push_cast; exact hlt
    exact_mod_cast hcast
  have hlt_card : R.card < A.card := by rw [hR_card]; exact hcard
  obtain ⟨d₁, hd₁, d₂, hd₂, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt_card hmaps
  exact ⟨d₁, hd₁, d₂, hd₂, hne, heq⟩

/-- **Candidate-Shift Pigeonhole Floor Certificates (Proposition 4(a)):**
Verifies in pure-kernel real arithmetic the positive bit-count margins for both the wide
(`k = 200,061, s = 126,225, m = 101,630, r = 98,451`) and tight
(`k = 92,000,000, s = 58,045,538, m = 46,736,000, r = 45,264,038`) witnesses, proving
`k_0 > 200,061` (wide) and `k_0 > 92,000,000` (tight), together with the upper cutoff
`42 * 300,000,000 * 2^{56} < 2^{90}` showing pigeonhole counting loses force by `3 × 10^8` bits. -/
theorem pigeonhole_floor_wide_tight_certs :
    let log2_3 := Real.log 3 / Real.log 2
    -- Wide witness: k = 200,061, s = 126,225, m + r = 200,081
    ((200081 : ℝ) < Real.logb 2 ((199 / 100 : ℝ) ^ 2 * (3 * 200061 / 4)) +
      126225 * log2_3 + (1 / 10 ^ 7 : ℝ) * 200061) ∧
    -- Tight witness: k = 92,000,000, s = 58,045,538, m + r = 92,000,038
    ((92000038 : ℝ) < Real.logb 2 ((199 / 100 : ℝ) ^ 2 * (3 * 92000000 / 4)) +
      58045538 * log2_3 + (1 / 10 ^ 7 : ℝ) * 92000000) ∧
    -- Tight pigeonhole force dies by k = 300,000,000:
    (42 * 300000000 * 2 ^ 56 < 2 ^ 90) := by
  intro log2_3
  have hlog2 := real_log_two_bounds
  have hlog3 := real_log_three_bounds
  have hlog2_3_lo : (1098612288 : ℝ) / 693147181 < log2_3 := by
    dsimp [log2_3]
    have h2pos : 0 < Real.log 2 := by linarith [hlog2.1]
    rw [div_lt_div_iff₀ (by norm_num) h2pos]
    nlinarith [hlog2.2, hlog3.1]
  have hwide_log : (115 / 6 : ℝ) < Real.logb 2 ((199 / 100 : ℝ) ^ 2 * (3 * 200061 / 4)) := by
    have h1 : (2 : ℝ) ^ (115 : ℕ) < ((199 / 100 : ℝ) ^ 2 * (3 * 200061 / 4)) ^ (6 : ℕ) := by norm_num
    have h2 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h1
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h2
    push_cast at h2; linarith
  have htight_log : (28 : ℝ) < Real.logb 2 ((199 / 100 : ℝ) ^ 2 * (3 * 92000000 / 4)) := by
    have h1 : (2 : ℝ) ^ (28 : ℕ) < (199 / 100 : ℝ) ^ 2 * (3 * 92000000 / 4) := by norm_num
    have h2 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h1
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h2
    push_cast at h2; linarith
  refine ⟨?_, ?_, by decide⟩
  · have hnum : (200081 : ℝ) < 115 / 6 + 126225 * (1098612288 / 693147181) + (1 / 10 ^ 7 : ℝ) * 200061 := by
      norm_num
    linarith [hwide_log, hlog2_3_lo, hnum]
  · have hnum : (92000038 : ℝ) < 28 + 58045538 * (1098612288 / 693147181) + (1 / 10 ^ 7 : ℝ) * 92000000 := by
      norm_num
    linarith [htight_log, hlog2_3_lo, hnum]

/-- **Dyadic Subgroup Obstruction (Proposition 4(b) Part 1):**
At `q_* = 5683676 / 10^7` and `p_* = q_*^2 / (q_*^2 + (1 - q_*)^2)`, the dyadic subgroup
pair rate `H * H_2(p_*) + 2 * θ * H_2(q_*)` strictly exceeds `1 - θ^2`
(where `H = H_2(log_3 2)` and `θ = 1 - H`). -/
theorem dyadic_subgroup_obstruction_cert :
    let H := binEntropy (Real.log 2 / Real.log 3)
    let θ := 1 - H
    let q_s : ℝ := 5683676 / 10 ^ 7
    let p_s : ℝ := q_s ^ 2 / (q_s ^ 2 + (1 - q_s) ^ 2)
    1 - θ ^ 2 < H * binEntropy p_s + 2 * θ * binEntropy q_s := by
  intro H θ q_s p_s
  have hH := lagarias_entropy_bounds
  have hH_lo : (949955 / 1000000 : ℝ) < H := by
    have h1 := hH.1; convert h1 using 1; norm_num
  have hH_hi : H < (949956 / 1000000 : ℝ) := by
    have h1 := hH.2; convert h1 using 1; norm_num
  have hps_lo : (6342256 / 10000000 : ℝ) ≤ p_s := by dsimp [p_s, q_s]; norm_num
  have hps_hi : p_s ≤ (6342257 / 10000000 : ℝ) := by dsimp [p_s, q_s]; norm_num
  have hps_pos : 0 < p_s := lt_of_lt_of_le (by norm_num) hps_lo
  have h1ps_pos : 0 < 1 - p_s := sub_pos.mpr (lt_of_le_of_lt hps_hi (by norm_num))
  have h1 := neg_logb2_ge_of_nat (k := 6342257) (d := 10 ^ 7) (sh := 0) (loNum := 656931) (scale := 10 ^ 6)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have h2 := neg_logb2_ge_of_nat (k := 3657744) (d := 10 ^ 7) (sh := 1) (loNum := 1450973) (scale := 10 ^ 6)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have h3 := neg_logb2_ge_of_nat (k := 5683676) (d := 10 ^ 7) (sh := 0) (loNum := 815103) (scale := 10 ^ 6)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have h4 := neg_logb2_ge_of_nat (k := 4316324) (d := 10 ^ 7) (sh := 1) (loNum := 1212124) (scale := 10 ^ 6)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hnlp : (656931 / 1000000 : ℝ) ≤ -Real.logb 2 p_s := by
    have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hps_pos hps_hi
    have h1' : (656931 / 1000000 : ℝ) ≤ -Real.logb 2 (6342257 / 10000000 : ℝ) := by
      have ha : ((656931 : ℕ) : ℝ) / ((10 ^ 6 : ℕ) : ℝ) = 656931 / 1000000 := by norm_num
      have hb : ((6342257 : ℕ) : ℝ) / ((10 ^ 7 : ℕ) : ℝ) = 6342257 / 10000000 := by norm_num
      rwa [ha, hb] at h1
    linarith [hm, h1']
  have hnl1p : (1450973 / 1000000 : ℝ) ≤ -Real.logb 2 (1 - p_s) := by
    have h1ps_hi : 1 - p_s ≤ 3657744 / 10000000 := by
      have : (6342256 / 10000000 : ℝ) + (3657744 / 10000000 : ℝ) = 1 := by norm_num
      linarith [hps_lo, this]
    have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) h1ps_pos h1ps_hi
    have h2' : (1450973 / 1000000 : ℝ) ≤ -Real.logb 2 (3657744 / 10000000 : ℝ) := by
      have ha : ((1450973 : ℕ) : ℝ) / ((10 ^ 6 : ℕ) : ℝ) = 1450973 / 1000000 := by norm_num
      have hb : ((3657744 : ℕ) : ℝ) / ((10 ^ 7 : ℕ) : ℝ) = 3657744 / 10000000 := by norm_num
      rwa [ha, hb] at h2
    linarith [hm, h2']
  have hHps : (947371 / 1000000 : ℝ) < binEntropy p_s := by
    unfold binEntropy crossEntropy
    have ha : (6342256 / 10000000 : ℝ) * (656931 / 1000000) ≤ p_s * (-Real.logb 2 p_s) :=
      mul_le_mul hps_lo hnlp (by norm_num) hps_pos.le
    have h1ps_lo : (3657743 / 10000000 : ℝ) ≤ 1 - p_s := by
      have : (6342257 / 10000000 : ℝ) + (3657743 / 10000000 : ℝ) = 1 := by norm_num
      linarith [hps_hi, this]
    have hb : (3657743 / 10000000 : ℝ) * (1450973 / 1000000) ≤ (1 - p_s) * (-Real.logb 2 (1 - p_s)) :=
      mul_le_mul h1ps_lo hnl1p (by norm_num) h1ps_pos.le
    have hnum : (947371 / 1000000 : ℝ) <
        (6342256 / 10000000 : ℝ) * (656931 / 1000000) + (3657743 / 10000000 : ℝ) * (1450973 / 1000000) := by
      norm_num
    linarith [ha, hb, hnum]
  have hHqs : (986470 / 1000000 : ℝ) < binEntropy q_s := by
    unfold binEntropy crossEntropy
    have h3' : (815103 / 1000000 : ℝ) ≤ -Real.logb 2 q_s := by
      have ha : ((815103 : ℕ) : ℝ) / ((10 ^ 6 : ℕ) : ℝ) = 815103 / 1000000 := by norm_num
      have hb : ((5683676 : ℕ) : ℝ) / ((10 ^ 7 : ℕ) : ℝ) = q_s := by dsimp [q_s]; norm_num
      rwa [ha, hb] at h3
    have h4' : (1212124 / 1000000 : ℝ) ≤ -Real.logb 2 (1 - q_s) := by
      have ha : ((1212124 : ℕ) : ℝ) / ((10 ^ 6 : ℕ) : ℝ) = 1212124 / 1000000 := by norm_num
      have hb : ((4316324 : ℕ) : ℝ) / ((10 ^ 7 : ℕ) : ℝ) = 1 - q_s := by dsimp [q_s]; norm_num
      rwa [ha, hb] at h4
    have hqa : q_s * (815103 / 1000000 : ℝ) ≤ q_s * (-Real.logb 2 q_s) :=
      mul_le_mul_of_nonneg_left h3' (by dsimp [q_s]; norm_num)
    have hqb : (1 - q_s) * (1212124 / 1000000 : ℝ) ≤ (1 - q_s) * (-Real.logb 2 (1 - q_s)) :=
      mul_le_mul_of_nonneg_left h4' (by dsimp [q_s]; norm_num)
    have hnum : (986470 / 1000000 : ℝ) <
        q_s * (815103 / 1000000 : ℝ) + (1 - q_s) * (1212124 / 1000000 : ℝ) := by
      dsimp [q_s]; norm_num
    linarith [hqa, hqb, hnum]
  have hterm1 : (949955 / 1000000 : ℝ) * (947371 / 1000000) < H * binEntropy p_s :=
    mul_lt_mul'' hH_lo hHps (by norm_num) (by norm_num)
  have hθ_lo : (1 - 949956 / 1000000 : ℝ) < θ := by dsimp [θ]; linarith [hH_hi]
  have hterm2 : (2 * (1 - 949956 / 1000000 : ℝ)) * (986470 / 1000000) < 2 * θ * binEntropy q_s :=
    mul_lt_mul'' (by linarith [hθ_lo]) hHqs (by norm_num) (by norm_num)
  have hθsq : (1 - 949956 / 1000000 : ℝ) ^ 2 < θ ^ 2 :=
    sq_lt_sq' (by linarith [hθ_lo]) hθ_lo
  have hnum : (1 : ℝ) - (1 - 949956 / 1000000 : ℝ) ^ 2 <
      (949955 / 1000000 : ℝ) * (947371 / 1000000) +
      (2 * (1 - 949956 / 1000000 : ℝ)) * (986470 / 1000000) := by
    norm_num
  calc 1 - θ ^ 2 < 1 - (1 - 949956 / 1000000 : ℝ) ^ 2 := by linarith [hθsq]
    _ < (949955 / 1000000 : ℝ) * (947371 / 1000000) +
        (2 * (1 - 949956 / 1000000 : ℝ)) * (986470 / 1000000) := hnum
    _ < H * binEntropy p_s + 2 * θ * binEntropy q_s := add_lt_add hterm1 hterm2

/-- **Scholar-Verified Nashida (2026, r7) Gain-Ratio Comparison:**
Proves in pure-kernel real arithmetic:
- `0.94476 < 0.945 < 0.9484 < H_2(log_3 2)`,
- Tight saving `H_2(log_3 2) - 0.94476 > 8.895 × 10^7 * (5.84 × 10^{-11})`,
- Wide saving `H_2(log_3 2) - 0.945 > 8.484 × 10^7 * (5.84 × 10^{-11})`,
- Stage-1 saving `H_2(log_3 2) - 0.9484 > 2.662 × 10^7 * (5.84 × 10^{-11})`. -/
theorem nashida_gain_ratio_gt_88M :
    let H := binEntropy (Real.log 2 / Real.log 3)
    let gNashida : ℝ := 584 / 10 ^ 13
    (94476 / 10 ^ 5 : ℝ) < 945 / 10 ^ 3 ∧
    (945 / 10 ^ 3 : ℝ) < 9484 / 10 ^ 4 ∧
    (9484 / 10 ^ 4 : ℝ) < H ∧
    88950000 * gNashida < H - 94476 / 10 ^ 5 ∧
    84840000 * gNashida < H - 945 / 10 ^ 3 ∧
    26620000 * gNashida < H - 9484 / 10 ^ 4 := by
  have hH := lagarias_entropy_bounds.1
  refine ⟨by norm_num, by norm_num, by linarith, by linarith, by linarith, by linarith⟩

/-- **Schlickewei (1990, p. 45, eq. (1.4)) vs. Schlickewei (1992, p. 246, eq. (1.4)) Identity:**
Verifies that the place-count notation shift `s_1990 = 2` finite primes (`s + 1 = 3` total places)
versus `s_1992 = 3` total places produces the IDENTICAL base `24` and exponent
`2^{52} * 3^6 * (2 / σ)^2` for both `σ = 10^{-4}` and `σ = 10^{-7}`. -/
theorem schlickewei_1990_vs_1992_eq :
    let s1990 : ℕ := 2
    let s1992 : ℕ := 3
    let n : ℕ := 2
    let d : ℕ := 1
    (8 * (s1990 + 1) * Nat.factorial d = 8 * s1992 * Nat.factorial d) ∧
    (8 * s1992 * Nat.factorial d = 24) ∧
    (∀ invDelta : ℕ,
      2 ^ (26 * n) * (s1990 + 1) ^ 6 * invDelta ^ 2 =
        2 ^ (26 * n) * s1992 ^ 6 * invDelta ^ 2) ∧
    (2 ^ (26 * n) * s1992 ^ 6 * 20000 ^ 2 = 1313249651341236633600000000) ∧
    (2 ^ (26 * n) * s1992 ^ 6 * 20000000 ^ 2 = 1313249651341236633600000000000000) := by
  refine ⟨by decide, by decide, fun _ => rfl, by decide, by decide⟩

/-- **Evertse (1996, p. 228, eq. (1.3)) Intermediate Line-Count Bounds (`< 10^{398}`, `< 10^{524}`):**
Formalizes the intermediate quantitative Subspace Theorem milestone (`n = 2, s = 3, D = 1`)
bridging Schlickewei (1990/1992) and Evertse–Ferretti (2013):
`(2^{60 n^2} * (2 / σ)^{7 n})^s * ln(4 D) * ln(ln(4 D)) < 10^{398}` (`σ = 10^{-4}`) and
`< 10^{524}` (`σ = 10^{-7}`). -/
theorem evertse_1996_line_counts :
    (((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 *
      Real.log 4 * Real.log (Real.log 4) < (10 : ℝ) ^ 398) ∧
    (((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 *
      Real.log 4 * Real.log (Real.log 4) < (10 : ℝ) ^ 524) := by
  have hlog2 := real_log_two_bounds
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlog4_gt1 : 1 < Real.log 4 := by rw [hlog4_eq]; linarith [hlog2.1]
  have hlog4_lt : Real.log 4 < 14 / 10 := by rw [hlog4_eq]; linarith [hlog2.2]
  have hll4_lt : Real.log (Real.log 4) < 4 / 10 := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log 4)
    linarith
  have hprod_lt1 : Real.log 4 * Real.log (Real.log 4) < 1 := by
    have hll4_pos : 0 < Real.log (Real.log 4) := Real.log_pos hlog4_gt1
    nlinarith
  have hwide_nat : (2 ^ 240 * 20000 ^ 14) ^ 3 < 10 ^ 398 := by decide +kernel
  have htight_nat : (2 ^ 240 * 20000000 ^ 14) ^ 3 < 10 ^ 524 := by decide +kernel
  have hwide_r : ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 < (10 : ℝ) ^ 398 := by
    exact_mod_cast hwide_nat
  have htight_r : ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 < (10 : ℝ) ^ 524 := by
    exact_mod_cast htight_nat
  constructor
  · calc ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 * Real.log 4 * Real.log (Real.log 4)
        = ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 * (Real.log 4 * Real.log (Real.log 4)) := by ring
      _ < ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 * 1 :=
          mul_lt_mul_of_pos_left hprod_lt1 (by positivity)
      _ = ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000 : ℝ) ^ (7 * 2)) ^ 3 := mul_one _
      _ < (10 : ℝ) ^ 398 := hwide_r
  · calc ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 * Real.log 4 * Real.log (Real.log 4)
        = ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 * (Real.log 4 * Real.log (Real.log 4)) := by ring
      _ < ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 * 1 :=
          mul_lt_mul_of_pos_left hprod_lt1 (by positivity)
      _ = ((2 : ℝ) ^ (60 * 2 ^ 2) * (20000000 : ℝ) ^ (7 * 2)) ^ 3 := mul_one _
      _ < (10 : ℝ) ^ 524 := htight_r

/-- **Scholar Trap #1 Diagnostic (`n = 3` vs. `n = 2` in Evertse–Ferretti 2013 eq. (3.10)):**
Confirms the exact inflation ratio `(2^{2*3} * 3^{14}) / (2^{2*2} * 2^{14}) = 3^{14} / 2^{12}
= 4782969 / 4096 > 1167` if one mistakenly substituted `|S| = 3` for ambient dimension `n = 2`. -/
theorem evertse_ferretti_n3_vs_n2_ratio :
    ((2 ^ (2 * 3) * 3 ^ 14 : ℚ) / (2 ^ (2 * 2) * 2 ^ 14 : ℚ) = 4782969 / 4096) ∧
    (1167 < (4782969 / 4096 : ℚ)) ∧
    ((4782969 / 4096 : ℚ) < 1168) := by
  norm_num

end CollatzTwoWindow
