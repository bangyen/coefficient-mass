/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.NbMode

/-!
# Moments of the Negative-Binomial Law

This module computes the moments behind the Chebyshev step of Lemma 3.4 of
`coefficient-mass-rows.tex`.  With `k = c + 1`, `P(j + k) = ϖ^k binom(j + c, c) r^{-j}`, and
`∑_j binom(j + m, m) x^j = (1 - x)^{-(m+1)}` gives `∑ P = 1`, mean `kr/(r - 1)`, and
`∑_t P(t) t (t + 1) = k(k + 1) r^2/(r - 1)^2`, hence variance `kr/(r - 1)^2`.

## Theorems

* `cast_choose_succ`.
* `nbLaw_eq`.
* `norm_one_div_lt`.
* `one_sub_one_div`.
* `hasSum_nbLaw`.
* `hasSum_nbLaw_mul`.
* `hasSum_nbLaw_mul_succ`.
* `hasSum_nbLaw_var`.
-/

namespace CoefficientMass

/-- `(a + c + 1) binom(a + c, c) = (c + 1) binom(a + c + 1, c + 1)`. -/
theorem cast_choose_succ (a c : ℕ) :
    ((a + (c + 1) : ℕ) : ℝ) * ((a + c).choose c : ℝ) =
      ((c + 1 : ℕ) : ℝ) * ((a + (c + 1)).choose (c + 1) : ℝ) := by
  have e : (a + c + 1) * (a + c).choose c = (a + c + 1).choose (c + 1) * (c + 1) :=
    Nat.succ_mul_choose_eq (a + c) c
  rw [← add_assoc]
  exact_mod_cast e.trans (Nat.mul_comm _ _)

/-- `P(j + c + 1) = (1 - 1/r)^{c+1} binom(j + c, c) r^{-j}`. -/
theorem nbLaw_eq {r : ℝ} (hr : 1 < r) (c j : ℕ) : nbLaw r (c + 1) (j + (c + 1)) =
    (1 - 1 / r) ^ (c + 1) * (((j + c).choose c : ℝ) * (1 / r) ^ j) := by
  have hr0 : r ≠ 0 := by positivity
  have hy : 1 - 1 / r = (r - 1) * (1 / r) := by rw [sub_mul, one_mul, mul_one_div_cancel hr0]
  unfold nbLaw prefixWeight
  rw [if_pos (by omega), show j + (c + 1) - 1 = j + c by omega, show c + 1 - 1 = c by omega,
    pow_add, hy, mul_pow]
  ring

theorem norm_one_div_lt {r : ℝ} (hr : 1 < r) : ‖1 / r‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact (div_lt_one (by linarith)).2 hr

theorem one_sub_one_div {r : ℝ} (hr : 1 < r) : 1 - 1 / r = (r - 1) / r := by
  have hr0 : r ≠ 0 := by positivity
  field_simp

/-- `∑_t P(t) = 1`. -/
theorem hasSum_nbLaw {r : ℝ} (hr : 1 < r) (c : ℕ) :
    HasSum (fun j => nbLaw r (c + 1) (j + (c + 1))) 1 := by
  have h1x : 1 - 1 / r ≠ 0 := by
    rw [one_sub_one_div hr]
    exact div_ne_zero (by linarith) (by positivity)
  convert (hasSum_choose_mul_geometric_of_norm_lt_one c (norm_one_div_lt hr)).mul_left
    ((1 - 1 / r) ^ (c + 1)) using 1
  · funext j
    exact nbLaw_eq hr c j
  · exact (mul_one_div_cancel (pow_ne_zero _ h1x)).symm

/-- `∑_t t P(t) = kr/(r - 1)`. -/
theorem hasSum_nbLaw_mul {r : ℝ} (hr : 1 < r) (c : ℕ) :
    HasSum (fun j => ((j + (c + 1) : ℕ) : ℝ) * nbLaw r (c + 1) (j + (c + 1)))
      (((c + 1 : ℕ) : ℝ) * r / (r - 1)) := by
  have hr0 : r ≠ 0 := by positivity
  have hr1 : r - 1 ≠ 0 := by linarith
  convert (hasSum_choose_mul_geometric_of_norm_lt_one (c + 1) (norm_one_div_lt hr)).mul_left
    (((c + 1 : ℕ) : ℝ) * (1 - 1 / r) ^ (c + 1)) using 1
  · funext j
    rw [nbLaw_eq hr c j]
    linear_combination (1 - 1 / r) ^ (c + 1) * (1 / r) ^ j * cast_choose_succ j c
  · rw [one_sub_one_div hr, pow_succ ((r - 1) / r) (c + 1), div_pow]
    field_simp

/-- `∑_t t (t + 1) P(t) = k(k + 1) r^2/(r - 1)^2`. -/
theorem hasSum_nbLaw_mul_succ {r : ℝ} (hr : 1 < r) (c : ℕ) :
    HasSum (fun j => ((j + (c + 1) : ℕ) : ℝ) * ((j + (c + 1 + 1) : ℕ) : ℝ) *
      nbLaw r (c + 1) (j + (c + 1)))
      (((c + 1 : ℕ) : ℝ) * ((c + 1 + 1 : ℕ) : ℝ) * r ^ 2 / (r - 1) ^ 2) := by
  have hr0 : r ≠ 0 := by positivity
  have hr1 : r - 1 ≠ 0 := by linarith
  convert (hasSum_choose_mul_geometric_of_norm_lt_one (c + 1 + 1) (norm_one_div_lt hr)).mul_left
    (((c + 1 : ℕ) : ℝ) * ((c + 1 + 1 : ℕ) : ℝ) * (1 - 1 / r) ^ (c + 1)) using 1
  · funext j
    rw [nbLaw_eq hr c j]
    linear_combination (1 - 1 / r) ^ (c + 1) * (1 / r) ^ j *
      (((j + (c + 1 + 1) : ℕ) : ℝ) * cast_choose_succ j c +
        ((c + 1 : ℕ) : ℝ) * cast_choose_succ j (c + 1))
  · rw [one_sub_one_div hr, pow_succ ((r - 1) / r) (c + 1 + 1), pow_succ ((r - 1) / r) (c + 1),
      div_pow]
    field_simp

/-- `∑_t (t - μ)^2 P(t) = kr/(r - 1)^2` with `μ = kr/(r - 1)`. -/
theorem hasSum_nbLaw_var {r : ℝ} (hr : 1 < r) (c : ℕ) :
    HasSum (fun j => nbLaw r (c + 1) (j + (c + 1)) *
      (((j + (c + 1) : ℕ) : ℝ) - ((c + 1 : ℕ) : ℝ) * r / (r - 1)) ^ 2)
      (((c + 1 : ℕ) : ℝ) * r / (r - 1) ^ 2) := by
  have hr1 : r - 1 ≠ 0 := by linarith
  set μ := ((c + 1 : ℕ) : ℝ) * r / (r - 1) with hμ
  convert ((hasSum_nbLaw_mul_succ hr c).sub ((hasSum_nbLaw_mul hr c).mul_left (2 * μ + 1))).add
    ((hasSum_nbLaw hr c).mul_left (μ ^ 2)) using 1
  · funext j
    have e : ((j + (c + 1 + 1) : ℕ) : ℝ) = ((j + (c + 1) : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e]
    ring
  · rw [hμ, Nat.cast_succ (c + 1)]
    field_simp
    ring

end CoefficientMass
