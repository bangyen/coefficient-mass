/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ValsSplit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Coefficient Bounds for Proposition 4.2

This module collects the estimates of Proposition 4.2 of `coefficient-mass.tex` on the
circle `|t| = R`.  For distinct `z ∈ Z ⊂ ℕ_{>0}` with `|Z| ≤ K`,
`∏_{z ∈ Z} |1 - d/z| ≤ ∏_{i ≤ K} (1 + d/i) = C(d + K, K)`; a real polynomial of degree at
most `D` has `|g(t)| ≤ ∑_{d ≤ D} |g_d| R^d`; and
`∑_{1 ≤ d ≤ D} C(d + K, K) R^d < (1 - R)^{-(K+1)} - 1`.

## Theorems

* `prod_one_add_div_eq_choose`.
* `prod_abs_le_choose`.
* `norm_eval_le_sum`.
* `sum_choose_lt`.
-/

open Polynomial

namespace CoefficientMass

/-- `∏_{j < m} (1 + d / (j + 1)) = C(d + m, m)`. -/
theorem prod_one_add_div_eq_choose (d : ℕ) : ∀ m : ℕ,
    ∏ j ∈ Finset.range m, (1 + (d : ℝ) / ((j : ℝ) + 1)) = ((d + m).choose m : ℝ) := by
  intro m
  induction m with
  | zero => rw [Finset.prod_range_zero, Nat.choose_zero_right, Nat.cast_one]
  | succ m ih =>
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have e := congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_choose_eq (d + m) m)
    push_cast at e
    rw [Finset.prod_range_succ, ih, show d + (m + 1) = d + m + 1 by ring, one_add_div hm,
      mul_div_assoc', div_eq_iff hm]
    push_cast
    linear_combination e

/-- `∏_{z ∈ Z} |1 - d/z| ≤ C(d + K, K)` for `Z ⊂ ℕ_{>0}` with `|Z| ≤ K`. -/
theorem prod_abs_le_choose (d : ℕ) (Z : Finset ℕ) (hZ : ∀ z ∈ Z, 1 ≤ z) {K : ℕ}
    (hK : Z.card ≤ K) : ∏ z ∈ Z, |1 - (d : ℝ) / z| ≤ ((d + K).choose K : ℝ) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : ∏ z ∈ Z, |1 - (d : ℝ) / z| ≤ ∏ z ∈ Z, (1 + (d : ℝ) / z) :=
    Finset.prod_le_prod (fun z _ => abs_nonneg _) fun z _ => by
      have : 0 ≤ (d : ℝ) / z := div_nonneg hd (Nat.cast_nonneg z)
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 := prod_le_prod_bot (h := fun x : ℕ => 1 + (d : ℝ) / x) (lo₀ := 1)
    (fun x _ => by positivity)
    (fun x y hx hxy => by
      have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
      have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
      have := div_le_div_of_nonneg_left hd (by linarith) hxy'
      linarith)
    Z.card 1 Z rfl le_rfl hZ
  have h3 : ∏ j ∈ Finset.range Z.card, (1 + (d : ℝ) / ((1 + j : ℕ) : ℝ)) =
      ((d + Z.card).choose Z.card : ℝ) := by
    rw [← prod_one_add_div_eq_choose]
    exact Finset.prod_congr rfl fun j _ => by push_cast; ring
  have h4 : ((d + Z.card).choose Z.card : ℝ) ≤ ((d + K).choose K : ℝ) := by
    rw [← Nat.choose_symm_add, ← Nat.choose_symm_add (m := d)]
    exact_mod_cast Nat.choose_le_choose d (by omega)
  exact h1.trans (h2.trans (h3.le.trans h4))

/-- `|g(t)| ≤ ∑_{d ≤ D} |g_d| R^d` on `|t| = R` for `g` of degree at most `D`. -/
theorem norm_eval_le_sum {g : ℝ[X]} {D : ℕ} (hdeg : ∀ d, D < d → g.coeff d = 0) {R : ℝ}
    {t : ℂ} (ht : ‖t‖ = R) :
    ‖(g.map (algebraMap ℝ ℂ)).eval t‖ ≤ ∑ d ∈ Finset.range (D + 1), |g.coeff d| * R ^ d := by
  rw [eval_eq_sum_range' (n := D + 1) (lt_of_le_of_lt (natDegree_map_le.trans
    (natDegree_le_iff_coeff_eq_zero.2 hdeg)) (Nat.lt_succ_self D))]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun d _ => ?_))
  rw [coeff_map, norm_mul, norm_pow, ht, Complex.coe_algebraMap, Complex.norm_real,
    Real.norm_eq_abs]

/-- `∑_{d < D} C(d + 1 + K, K) R^{d+1} < (1 - R)^{-(K+1)} - 1` for `0 < R < 1`. -/
theorem sum_choose_lt {R : ℝ} (h0 : 0 < R) (h1 : R < 1) (K D : ℕ) :
    ∑ d ∈ Finset.range D, ((d + 1 + K).choose K : ℝ) * R ^ (d + 1) <
      1 / (1 - R) ^ (K + 1) - 1 := by
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) K
    (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)
  have hle := sum_le_hasSum (Finset.range (D + 1 + 1))
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0.le _)) hs
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at hle
  have hpos : (0 : ℝ) < ((D + 1 + K).choose K : ℝ) * R ^ (D + 1) :=
    mul_pos (by exact_mod_cast Nat.choose_pos (by omega)) (pow_pos h0 _)
  rw [Nat.zero_add, Nat.choose_self, Nat.cast_one, pow_zero, mul_one] at hle
  linarith

end CoefficientMass
