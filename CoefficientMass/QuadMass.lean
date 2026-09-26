/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Mass
import CoefficientMass.QuadMain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quadratic Mass at Every Root Set

This module finishes Proposition 4.2 of `coefficient-mass.tex`: `Λ(F) ≥ L^2 / 80` for a
monic multiple `F` of `∏ (x - r_i)` with `r_i ≥ 2` and `L ≥ 8`.  With `R = 9/10` and
`k = ⌊L/8⌋`, the bound (4.4) exceeds `e^{L/5}`, because `(9/5)^7 > 61` and
`e^{8/5} < 5`; so at least `⌊L/8⌋ ≥ L/16` coefficients have `log |f_j| ≥ L/5`.

## Definitions

* `QuadraticMass`.

## Theorems

* `largeCount_mul_log_le_mass`.
* `exp_le_rows`.
* `quadraticMass`.
-/

open Polynomial

namespace CoefficientMass

/-- Proposition 4.2: `Λ(F) ≥ L^2 / 80` for a monic real multiple `F` of `∏ (x - r_i)` with
`r_i ≥ 2` and `L ≥ 8`. -/
def QuadraticMass : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), F.Monic → (∀ i, 2 ≤ r i) → rootProduct ℝ r ∣ F →
    8 ≤ L → (L : ℝ) ^ 2 / 80 ≤ mass (F.map (algebraMap ℝ ℂ))

/-- `k` coefficients of size at least `T ≥ 1` give mass at least `k log T`. -/
theorem largeCount_mul_log_le_mass (F : ℝ[X]) {T : ℝ} (hT : 1 ≤ T) :
    (largeCount F T : ℝ) * Real.log T ≤ mass (F.map (algebraMap ℝ ℂ)) := by
  rw [mass_eq_sum_range, natDegree_map, largeCount]
  set S := (Finset.range F.natDegree).filter fun j => T ≤ ‖F.coeff j‖
  have hsub : S ⊆ Finset.range (F.natDegree + 1) := fun j hj => Finset.mem_range.2 (by
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    omega)
  calc (S.card : ℝ) * Real.log T = ∑ _j ∈ S, Real.log T := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ S, logPlus ‖(F.map (algebraMap ℝ ℂ)).coeff j‖ := Finset.sum_le_sum fun j hj => by
        rw [coeff_map, Complex.coe_algebraMap, Complex.norm_real]
        exact (Real.log_le_log (by linarith) (Finset.mem_filter.1 hj).2).trans
          (le_max_right _ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => logPlus_nonneg _

/-- `e^{(8K + ρ)/5} ≤ ((9/5)^{7K+ρ+1} - 1) / (10^K - 1)` for `K ≥ 1`. -/
theorem exp_le_rows (K ρ : ℕ) (hK : 1 ≤ K) :
    Real.exp (((8 * K + ρ : ℕ) : ℝ) / 5) ≤
      ((9 / 5 : ℝ) ^ (7 * K + ρ + 1) - 1) / (10 ^ K - 1) := by
  have h10 : (1 : ℝ) < 10 ^ K := one_lt_pow₀ (by norm_num) (by omega)
  rw [le_div_iff₀ (by linarith)]
  have he1 := Real.exp_one_lt_d9
  have ha : Real.exp (8 / 5) < 5 := by
    have e : Real.exp (8 / 5) ^ 5 = Real.exp 1 ^ 8 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have : Real.exp 1 ^ 8 < 5 ^ 5 :=
      (pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num)).trans (by norm_num)
    rw [← e] at this
    exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 this
  have hb : Real.exp (1 / 5) < 9 / 5 := by
    have e : Real.exp (1 / 5) ^ 5 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have : Real.exp 1 < (9 / 5) ^ 5 := he1.trans (by norm_num)
    rw [← e] at this
    exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 this
  have he : Real.exp (((8 * K + ρ : ℕ) : ℝ) / 5) =
      Real.exp (8 / 5) ^ K * Real.exp (1 / 5) ^ ρ := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hA : Real.exp (8 / 5) ^ K ≤ 5 ^ K := pow_le_pow_left₀ (Real.exp_pos _).le ha.le K
  have hB : Real.exp (1 / 5) ^ ρ ≤ (9 / 5) ^ ρ := pow_le_pow_left₀ (Real.exp_pos _).le hb.le ρ
  have hu : (1 : ℝ) ≤ (9 / 5) ^ ρ := one_le_pow₀ (by norm_num)
  have hW : (50 : ℝ) ^ K ≤ ((9 / 5 : ℝ) ^ 7) ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
  have hQ : (50 : ℝ) ≤ 50 ^ K := by
    calc (50 : ℝ) = 50 ^ 1 := (pow_one _).symm
      _ ≤ 50 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have hPT : (5 : ℝ) ^ K * 10 ^ K = 50 ^ K := by rw [← mul_pow]; norm_num
  have hpow : (9 / 5 : ℝ) ^ (7 * K + ρ + 1) = ((9 / 5 : ℝ) ^ 7) ^ K * (9 / 5) ^ ρ * (9 / 5) := by
    rw [pow_succ, pow_add, pow_mul]
  rw [he, hpow]
  set u := (9 / 5 : ℝ) ^ ρ
  have hE0 : 0 ≤ Real.exp (1 / 5) ^ ρ := by positivity
  have h1 : Real.exp (8 / 5) ^ K * Real.exp (1 / 5) ^ ρ * (10 ^ K - 1) ≤
      5 ^ K * u * (10 ^ K - 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hA hB hE0 (by positivity)) (by linarith)
  have h2 : (5 : ℝ) ^ K * u * (10 ^ K - 1) = 50 ^ K * u - 5 ^ K * u := by
    rw [← hPT]
    ring
  have h3 : (50 : ℝ) ^ K * u ≤ ((9 / 5 : ℝ) ^ 7) ^ K * u :=
    mul_le_mul_of_nonneg_right hW (by linarith)
  have h4 : (50 : ℝ) ≤ 50 ^ K * u := by nlinarith
  have h5 : (0 : ℝ) ≤ 5 ^ K * u := by positivity
  nlinarith

/-- Proposition 4.2: `Λ(F) ≥ L^2 / 80` for `L ≥ 8`. -/
theorem quadraticMass : QuadraticMass := by
  intro L r F hF hr hdvd hL
  set K := L / 8 with hK
  have hK1 : 1 ≤ K := by omega
  have hrow := jensenRows L K r F hF hr hdvd hK1 (by omega) (9 / 10) (by norm_num) (by norm_num)
  have hY : Real.exp ((L : ℝ) / 5) ≤
      ((2 * (9 / 10 : ℝ)) ^ (L - K + 1) - 1) / (1 / (1 - 9 / 10 : ℝ) ^ K - 1) := by
    have h := exp_le_rows K (L % 8) hK1
    rw [show 8 * K + L % 8 = L by omega, show 7 * K + L % 8 + 1 = L - K + 1 by omega] at h
    rw [show (2 : ℝ) * (9 / 10) = 9 / 5 by norm_num, show (1 : ℝ) / (1 - 9 / 10) ^ K = 10 ^ K by
      rw [show (1 : ℝ) - 9 / 10 = 1 / 10 by norm_num, div_pow, one_pow, one_div_one_div]]
    exact h
  have hcount : K ≤ largeCount F (Real.exp ((L : ℝ) / 5)) :=
    hrow.trans (Finset.card_le_card fun j hj => Finset.mem_filter.2
      ⟨(Finset.mem_filter.1 hj).1, hY.trans (Finset.mem_filter.1 hj).2⟩)
  have hmass := largeCount_mul_log_le_mass F (Real.one_le_exp (by positivity) :
    1 ≤ Real.exp ((L : ℝ) / 5))
  rw [Real.log_exp] at hmass
  have hK16 : (L : ℝ) ≤ 16 * K := by exact_mod_cast (show L ≤ 16 * K by omega)
  have hKc : (K : ℝ) ≤ largeCount F (Real.exp ((L : ℝ) / 5)) := by exact_mod_cast hcount
  have hL0 : (0 : ℝ) ≤ L / 5 := by positivity
  calc (L : ℝ) ^ 2 / 80 = (L / 16) * (L / 5) := by ring
    _ ≤ K * (L / 5) := mul_le_mul_of_nonneg_right (by linarith) hL0
    _ ≤ largeCount F (Real.exp ((L : ℝ) / 5)) * (L / 5) := mul_le_mul_of_nonneg_right hKc hL0
    _ ≤ _ := hmass

end CoefficientMass
