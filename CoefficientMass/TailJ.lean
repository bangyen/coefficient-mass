/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A Beta Bound on `[0, 1]`

This module bounds the last integral of Lemma 4.11 of `coefficient-mass.tex`:
`J(a, b) = ∫_0^1 t^a (1 + t)^{-b} dt ≤ B(a + 1, b - a - 1) = a! (b - a - 2)! / (b - 1)!`.
The derivative of `t^{a+1} (1 + t)^{-b}` gives
`b J(a + 1, b + 1) + 2^{-b} = (a + 1) J(a, b)`, and `J(0, b + 1) ≤ 1 / b`; the boundary
term only helps.

## Definitions

* `jI`.

## Theorems

* `intervalIntegrable_jI`.
* `jI_succ`.
* `jI_zero_le`.
* `jI_le`.
-/

open intervalIntegral

namespace CoefficientMass

/-- `J(a, b) = ∫_0^1 t^a / (1 + t)^b dt`. -/
noncomputable def jI (a b : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ a / (1 + t) ^ b

theorem intervalIntegrable_jI (a b : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ a / (1 + t) ^ b) MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
    fun t ht => ?_)
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact pow_ne_zero _ (by linarith [ht.1])

/-- `(c + 1) J(a + 1, c + 2) + 2^{-(c+1)} = (a + 1) J(a, c + 1)`. -/
theorem jI_succ (a c : ℕ) :
    ((c : ℝ) + 1) * jI (a + 1) (c + 2) + (1 / 2) ^ (c + 1) = ((a : ℝ) + 1) * jI a (c + 1) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t ^ (a + 1) / (1 + t) ^ (c + 1))
      (((a : ℝ) + 1) * (t ^ a / (1 + t) ^ (c + 1)) -
        ((c : ℝ) + 1) * (t ^ (a + 1) / (1 + t) ^ (c + 2))) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1t : (1 + t) ≠ 0 := by linarith [ht.1]
    have hd := (hasDerivAt_pow (a + 1) t).div (((hasDerivAt_id' t).const_add 1).fun_pow (c + 1))
      (pow_ne_zero _ h1t)
    convert hd using 1
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hint := ((intervalIntegrable_jI a (c + 1)).const_mul ((a : ℝ) + 1)).sub
    ((intervalIntegrable_jI (a + 1) (c + 2)).const_mul ((c : ℝ) + 1))
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [integral_sub ((intervalIntegrable_jI a (c + 1)).const_mul _)
    ((intervalIntegrable_jI (a + 1) (c + 2)).const_mul _), integral_const_mul,
    integral_const_mul] at h
  rw [jI, jI]
  norm_num at h ⊢
  linarith

/-- `J(0, c + 2) ≤ 1 / (c + 1)`. -/
theorem jI_zero_le (c : ℕ) : jI 0 (c + 2) ≤ 1 / ((c : ℝ) + 1) := by
  have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -(1 / ((c : ℝ) + 1)) * ((1 + t) ^ (c + 1))⁻¹)
        (t ^ 0 / (1 + t) ^ (c + 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1t : (1 + t) ≠ 0 := by linarith [ht.1]
    have hd := ((((hasDerivAt_id' t).const_add 1).fun_pow (c + 1)).inv
      (pow_ne_zero _ h1t)).const_mul (-(1 / ((c : ℝ) + 1)))
    convert hd using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have h := integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_jI 0 (c + 2))
  rw [jI, h, add_zero, one_pow, inv_one]
  have h3 : 0 ≤ 1 / ((c : ℝ) + 1) * ((1 + 1 : ℝ) ^ (c + 1))⁻¹ := by positivity
  linarith

/-- `J(a, c + 2) ≤ a! (c - a)! / (c + 1)!` for `a ≤ c`. -/
theorem jI_le : ∀ a c : ℕ, a ≤ c →
    jI a (c + 2) ≤ (a.factorial * (c - a).factorial : ℝ) / (c + 1).factorial := by
  intro a
  induction a with
  | zero =>
    intro c _
    refine (jI_zero_le c).trans (le_of_eq ?_)
    rw [Nat.factorial_zero, Nat.sub_zero, Nat.factorial_succ,
      div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    ring
  | succ a ih =>
    intro c hac
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have h := jI_succ a (c + 1)
    rw [show c + 1 + 1 = c + 2 from rfl] at h
    have hb := ih c (by omega)
    have hf : (0 : ℝ) < c.factorial := by positivity
    have hf1 : (0 : ℝ) < (c + 1).factorial := by positivity
    have hp : (0 : ℝ) < (1 / 2) ^ (c + 2) := by positivity
    rw [le_div_iff₀ hf1] at hb
    rw [show c + 1 - (a + 1) = c - a by omega, Nat.factorial_succ (c + 1), Nat.factorial_succ a,
      le_div_iff₀ (by positivity)]
    push_cast at h ⊢
    have h1 : ((c : ℝ) + 1 + 1) * jI (a + 1) (c + 1 + 2) ≤ ((a : ℝ) + 1) * jI a (c + 2) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hf1.le
    have h3 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1)
    nlinarith

end CoefficientMass
