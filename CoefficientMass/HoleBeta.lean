/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Integrals of the Hole Formula

This module evaluates the two families of integrals in Lemma 4.7 of
`coefficient-mass.tex`: the Beta integral
`∫_0^1 v^a (1 - v)^b dv = a! b! / (a + b + 1)!`, and the integral
`J(a, b) = ∫_0^1 v^a (1 + v)^b dv` through the relation
`(a + b + 2) J(a + 1, b) + (a + 1) J(a, b) = 2^{b + 1}`, which is the
recursion the tail sums of the hole formula satisfy.

## Definitions

* `betaI`.
* `plusI`.

## Theorems

* `betaI_zero`.
* `betaI_succ`.
* `betaI_eq`.
* `plusI_zero`.
* `plusI_succ`.
* `plusI_rec`.
* `plusI_zero_left`.
-/

open intervalIntegral

namespace CoefficientMass

/-- `∫_0^1 v^a (1 - v)^b dv`. -/
noncomputable def betaI (a b : ℕ) : ℝ :=
  ∫ v in (0 : ℝ)..1, v ^ a * (1 - v) ^ b

/-- `∫_0^1 v^a (1 + v)^b dv`. -/
noncomputable def plusI (a b : ℕ) : ℝ :=
  ∫ v in (0 : ℝ)..1, v ^ a * (1 + v) ^ b

theorem betaI_zero (a : ℕ) : betaI a 0 = 1 / (a + 1) := by
  rw [betaI]
  simp only [pow_zero, mul_one]
  rw [integral_pow]
  norm_num

theorem betaI_succ (a b : ℕ) : betaI a (b + 1) = betaI a b - betaI (a + 1) b := by
  have h1 := (by fun_prop : Continuous fun v : ℝ => v ^ a * (1 - v) ^ b).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have h2 := (by fun_prop : Continuous fun v : ℝ =>
    v ^ (a + 1) * (1 - v) ^ b).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [betaI, betaI, betaI, ← integral_sub h1 h2]
  exact integral_congr fun v _ => by ring

/-- The Beta integral `∫_0^1 v^a (1 - v)^b dv = a! b! / (a + b + 1)!`. -/
theorem betaI_eq (a b : ℕ) :
    betaI a b = (a.factorial * b.factorial : ℝ) / (a + b + 1).factorial := by
  induction b generalizing a with
  | zero =>
    rw [betaI_zero, Nat.add_zero, Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  | succ b ih =>
    rw [betaI_succ, ih, ih, show a + 1 + b + 1 = a + b + 1 + 1 by ring,
      show a + (b + 1) + 1 = a + b + 1 + 1 by ring]
    push_cast [Nat.factorial_succ]
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring

theorem plusI_zero (a : ℕ) : plusI a 0 = 1 / (a + 1) := by
  rw [plusI]
  simp only [pow_zero, mul_one]
  rw [integral_pow]
  norm_num

theorem plusI_succ (a b : ℕ) : plusI a (b + 1) = plusI a b + plusI (a + 1) b := by
  have h1 := (by fun_prop : Continuous fun v : ℝ => v ^ a * (1 + v) ^ b).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have h2 := (by fun_prop : Continuous fun v : ℝ =>
    v ^ (a + 1) * (1 + v) ^ b).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [plusI, plusI, plusI, ← integral_add h1 h2]
  exact integral_congr fun v _ => by ring

/-- `(a + b + 2) J(a + 1, b) + (a + 1) J(a, b) = 2^{b + 1}`. -/
theorem plusI_rec (b : ℕ) :
    ∀ a : ℕ, ((a : ℝ) + b + 2) * plusI (a + 1) b + ((a : ℝ) + 1) * plusI a b = 2 ^ (b + 1) := by
  induction b with
  | zero =>
    intro a
    have h1 : ((a : ℝ) + 2) * plusI (a + 1) 0 = 1 := by
      rw [plusI_zero, mul_one_div, div_eq_one_iff_eq (by positivity)]
      push_cast
      ring
    have h2 : ((a : ℝ) + 1) * plusI a 0 = 1 := by
      rw [plusI_zero, mul_one_div, div_eq_one_iff_eq (by positivity)]
    push_cast
    linear_combination h1 + h2
  | succ b ih =>
    intro a
    have h1 := ih a
    have h2 := ih (a + 1)
    rw [plusI_succ, plusI_succ]
    push_cast at h2 ⊢
    linear_combination h1 + h2

theorem plusI_zero_left (j : ℕ) : plusI 0 j = (2 ^ (j + 1) - 1) / (j + 1) := by
  rw [plusI]
  simp only [pow_zero, one_mul]
  rw [integral_comp_add_left (fun x : ℝ => x ^ j), integral_pow]
  norm_num

end CoefficientMass
