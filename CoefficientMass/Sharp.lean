/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Chain
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sharpness of the Second Row at `(2, 3)`

This module proves Proposition 4.4 of `coefficient-mass.tex`: the multiples
`F_n = x^{n+1} - a_n x^n + t_n ∑_{j < n} x^j` of `(x - 2)(x - 3)` have
`b_2(F_n) = t_n`, and `t_n` decreases to `2`, the value Theorem 3.2 gives for
the row `k = 2`.  So `2` is the infimum of `b_2` over monic multiples.

## Definitions

* `sharpT`.
* `sharpA`.
* `sharpF`.
* `SharpRowTwo`.

## Theorems

* `sharpD_bounds`.
* `sharpT_bounds`.
* `coeff_sharpF`.
* `natDegree_sharpF`.
* `monic_sharpF`.
* `dvd_sharpF`.
* `largeCount_sharpT`.
* `largeCount_gt_sharpT`.
* `sharpT_lt_succ`.
* `tendsto_sharpT`.
* `rowTwo_ge_two`.
* `sharpRowTwo`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `t_n = 2 / (1 - 2^{1-n} + 3^{-n})`. -/
noncomputable def sharpT (n : ℕ) : ℝ :=
  2 / (1 - 2 * (1 / 2) ^ n + (1 / 3) ^ n)

/-- `a_n = 2 + t_n (1 - 2^{-n})`. -/
noncomputable def sharpA (n : ℕ) : ℝ :=
  2 + sharpT n * (1 - (1 / 2) ^ n)

/-- `F_n = x^{n+1} - a_n x^n + t_n ∑_{j < n} x^j`. -/
noncomputable def sharpF (n : ℕ) : ℝ[X] :=
  X ^ (n + 1) - C (sharpA n) * X ^ n + C (sharpT n) * ∑ j ∈ Finset.range n, X ^ j

/-- Proposition 4.4 (sharpness of the row `k = 2` at `(2, 3)`): every monic
multiple of `(x - 2)(x - 3)` has `b_2 ≥ 2`; for `n ≥ 2` the multiple `F_n`
has `b_2(F_n) = t_n > 2`; and `t_n` decreases to `2`. -/
def SharpRowTwo : Prop :=
  (∀ F : ℝ[X], F.Monic → (X - C 2) * (X - C 3) ∣ F → 2 ≤ largeCount F 2) ∧
    (∀ n, 2 ≤ n → (sharpF n).Monic ∧ (X - C 2) * (X - C 3) ∣ sharpF n ∧
      2 ≤ largeCount (sharpF n) (sharpT n) ∧
      (∀ T, sharpT n < T → largeCount (sharpF n) T ≤ 1) ∧
      2 < sharpT n ∧ sharpT (n + 1) < sharpT n) ∧
    Tendsto sharpT atTop (𝓝 2)

theorem sharpD_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 / 2 ≤ 1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n ∧
      1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n < 1 := by
  have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h3 : (1 / 3 : ℝ) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h3' : 0 < (1 / 3 : ℝ) ^ n := by positivity
  have h2' : 0 < (1 / 2 : ℝ) ^ n := by positivity
  constructor <;> nlinarith

theorem sharpT_bounds {n : ℕ} (hn : 2 ≤ n) : 2 < sharpT n ∧ sharpT n ≤ 4 := by
  obtain ⟨h1, h2⟩ := sharpD_bounds hn
  have hd : 0 < 1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n := by linarith
  rw [sharpT]
  constructor
  · rw [lt_div_iff₀ hd]
    linarith
  · rw [div_le_iff₀ hd]
    linarith

theorem coeff_sharpF (n j : ℕ) :
    (sharpF n).coeff j =
      if j = n + 1 then 1 else if j = n then -sharpA n else if j < n then sharpT n else 0 := by
  simp only [sharpF, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul,
    finset_sum_coeff, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs <;> first | omega | ring

theorem natDegree_sharpF (n : ℕ) : (sharpF n).natDegree = n + 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [coeff_sharpF, if_pos rfl]; norm_num)
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have : n + 1 < j := by exact_mod_cast hj
  rw [coeff_sharpF, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem monic_sharpF (n : ℕ) : (sharpF n).Monic := by
  rw [Monic, leadingCoeff, natDegree_sharpF, coeff_sharpF, if_pos rfl]

theorem eval_geom (x : ℝ) (n : ℕ) (hx : x ≠ 1) :
    (∑ j ∈ Finset.range n, (X : ℝ[X]) ^ j).eval x = (x ^ n - 1) / (x - 1) := by
  rw [eval_finset_sum]
  simp only [eval_pow, eval_X]
  exact geom_sum_eq hx n

theorem dvd_sharpF {n : ℕ} (hn : 2 ≤ n) : (X - C 2) * (X - C 3) ∣ sharpF n := by
  obtain ⟨h1, _⟩ := sharpD_bounds hn
  have hd : (1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n) ≠ 0 := by linarith
  have hu : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hv : (3 : ℝ) ^ n * (1 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
  have ht : sharpT n * (1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n) = 2 := div_mul_cancel₀ 2 hd
  have hr2 : (sharpF n).IsRoot 2 := by
    simp only [IsRoot, sharpF, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      eval_geom 2 n (by norm_num), sharpA]
    linear_combination sharpT n * hu
  have hr3 : (sharpF n).IsRoot 3 := by
    simp only [IsRoot, sharpF, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      eval_geom 3 n (by norm_num), sharpA]
    refine mul_right_cancel₀ hd ?_
    linear_combination (-(1 - (1 / 2 : ℝ) ^ n) * 3 ^ n + (3 ^ n - 1) / 2) * ht + hv
  have hQ := mul_divByMonic_eq_iff_isRoot.2 hr2
  have hQ3 : (sharpF n /ₘ (X - C 2)).IsRoot 3 := by
    have h := hr3
    rw [← hQ, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at h
    rw [IsRoot]
    linarith
  exact ⟨_, by rw [mul_assoc, mul_divByMonic_eq_iff_isRoot.2 hQ3, hQ]⟩

theorem abs_coeff_sharpF {n j : ℕ} (hn : 2 ≤ n) (hj : j < n + 1) :
    sharpT n ≤ ‖(sharpF n).coeff j‖ ∧ (j ≠ n → ‖(sharpF n).coeff j‖ = sharpT n) := by
  obtain ⟨ht2, ht4⟩ := sharpT_bounds hn
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1 / 4 := by norm_num
  rw [coeff_sharpF, if_neg (by omega), Real.norm_eq_abs]
  by_cases hjn : j = n
  · rw [if_pos hjn, abs_neg, sharpA]
    refine ⟨?_, fun h => absurd hjn h⟩
    rw [abs_of_pos (by nlinarith)]
    nlinarith
  · rw [if_neg hjn, if_pos (by omega), abs_of_pos (by linarith)]
    exact ⟨le_rfl, fun _ => rfl⟩

theorem largeCount_sharpT {n : ℕ} (hn : 2 ≤ n) : 2 ≤ largeCount (sharpF n) (sharpT n) := by
  rw [largeCount, natDegree_sharpF, Finset.filter_true_of_mem fun j hj =>
    (abs_coeff_sharpF hn (Finset.mem_range.1 hj)).1, Finset.card_range]
  omega

theorem largeCount_gt_sharpT {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : sharpT n < T) :
    largeCount (sharpF n) T ≤ 1 := by
  rw [largeCount, natDegree_sharpF]
  refine (Finset.card_le_card fun j hj => ?_).trans (Finset.card_singleton n).le
  rw [Finset.mem_filter, Finset.mem_range] at hj
  rw [Finset.mem_singleton]
  by_contra hjn
  have := (abs_coeff_sharpF hn hj.1).2 hjn
  linarith [hj.2]

theorem sharpT_lt_succ {n : ℕ} (hn : 2 ≤ n) : sharpT (n + 1) < sharpT n := by
  obtain ⟨h1, _⟩ := sharpD_bounds hn
  obtain ⟨h1', _⟩ := sharpD_bounds (by omega : 2 ≤ n + 1)
  rw [sharpT, sharpT, div_lt_div_iff_of_pos_left (by norm_num) (by linarith) (by linarith)]
  have h3 : (1 / 3 : ℝ) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h2 : 0 < (1 / 2 : ℝ) ^ n := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

theorem tendsto_sharpT : Tendsto sharpT atTop (𝓝 2) := by
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num)
  have hd : Tendsto (fun n => 1 - 2 * (1 / 2 : ℝ) ^ n + (1 / 3) ^ n) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (h2.const_mul 2)).add h3
    rwa [mul_zero, sub_zero, add_zero] at this
  have h := (hd.inv₀ one_ne_zero).const_mul (2 : ℝ)
  rw [inv_one, mul_one] at h
  exact h.congr fun n => (div_eq_mul_inv _ _).symm

/-- The row `k = 2` of Theorem 3.2 at `(2, 3)`. -/
theorem rowTwo_ge_two (F : ℝ[X]) (hF : F.Monic) (hdvd : (X - C 2) * (X - C 3) ∣ F) :
    2 ≤ largeCount F 2 := by
  have h := orderStatistics 2 ![2, 3] F (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | norm_num | exact absurd hij (by decide))
    (by intro i; fin_cases i <;> norm_num) hF.ne_zero
    (by
      simpa only [rootProduct, Algebra.algebraMap_self, RingHom.id_apply, Fin.prod_univ_two,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hdvd) 1
  have hp : ∏ i ∈ Finset.univ.filter ((1 : Fin 2) ≤ ·), (![(2 : ℝ), 3] i - 1) = 2 := by
    rw [show Finset.univ.filter ((1 : Fin 2) ≤ ·) = {1} by decide]
    norm_num
  rw [hp, hF.leadingCoeff, norm_one, one_mul] at h
  simpa only [ge_iff_le, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.reduceAdd] using h

theorem sharpRowTwo : SharpRowTwo :=
  ⟨rowTwo_ge_two, fun _ hn => ⟨monic_sharpF _, dvd_sharpF hn, largeCount_sharpT hn,
    fun _ hT => largeCount_gt_sharpT hn hT, (sharpT_bounds hn).1, sharpT_lt_succ hn⟩,
    tendsto_sharpT⟩

end CoefficientMass
