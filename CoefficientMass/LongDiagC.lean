/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LongDiag
import CoefficientMass.LongDiagB
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Long Diagonals Past a Linear Threshold

This module proves Proposition 6.8(c) of `coefficient-mass-rows.tex`.  With `m = n - 1`,
`binom(M + m, m) ≤ (e(M + m)/m)^m`, and `(1 + b/x)^x` increases in `x` (Bernoulli's
inequality); with `m ≤ k/α` and `M_k ≤ kr/(r - 1)` this gives
`Ξ(k) ≤ ρ(α)^k (4√(kr)/(r - 1) + 1)`, where `ρ(α) = θ (2re(αr/(r - 1) + 1))^{1/α}`.  When
`ρ(α) < 1` the right side is eventually below `3(2 - r)^2/r^2`.

## Definitions

* `rhoR`.

## Theorems

* `one_add_div_rpow_le`.
* `pow_choose_le`.
* `rhoR_nonneg`.
* `rhoR_pow`.
* `xiK_le_rho`.
* `exists_rho_small`.
* `longDiagC`.
-/

namespace CoefficientMass

/-- `ρ(α) = θ (2re(αr/(r - 1) + 1))^{1/α}`. -/
noncomputable def rhoR (r α : ℝ) : ℝ :=
  4 * (r - 1) / r ^ 2 * (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ (1 / α)

/-- `(1 + b/x)^x ≤ (1 + b/y)^y` for `b ≥ 0` and `0 < x ≤ y`. -/
theorem one_add_div_rpow_le {b x y : ℝ} (hb : 0 ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    (1 + b / x) ^ x ≤ (1 + b / y) ^ y := by
  have hy : 0 < y := hx.trans_le hxy
  have h := Real.one_add_mul_self_le_rpow_one_add (s := b / y)
    (by have : 0 ≤ b / y := by positivity
        linarith) (p := y / x) (by rw [le_div_iff₀ hx]; linarith)
  rw [div_mul_div_comm, mul_comm y b, mul_div_mul_right _ _ hy.ne'] at h
  calc (1 + b / x) ^ x ≤ ((1 + b / y) ^ (y / x)) ^ x := Real.rpow_le_rpow (by positivity) h hx.le
    _ = (1 + b / y) ^ y := by rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hx.ne']

/-- `c^m binom(M + m, m) ≤ (ce(1 + K/y))^y` for `c ≥ 1`, `1 ≤ m ≤ y` and `M ≤ K`. -/
theorem pow_choose_le {c K y : ℝ} (hc : 1 ≤ c) {M m : ℕ} (hm : 1 ≤ m) (hMK : (M : ℝ) ≤ K)
    (hmy : (m : ℝ) ≤ y) :
    c ^ m * ((M + m).choose m : ℝ) ≤ (c * Real.exp 1 * (1 + K / y)) ^ y := by
  have hc0 : 0 < c := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : 0 < y := hm0.trans_le hmy
  have hK : 0 ≤ K := (Nat.cast_nonneg M).trans hMK
  have h1 : ((M + m).choose m : ℝ) ≤ ((M : ℝ) + m) ^ m / m.factorial := by
    have := Nat.choose_le_pow_div (α := ℝ) m (M + m)
    push_cast at this
    exact this
  have h2 : (m : ℝ) ^ m / m.factorial ≤ Real.exp m := Real.pow_div_factorial_le_exp hm0.le m
  have h3 : ((M : ℝ) + m) ^ m / m.factorial =
      (1 + (M : ℝ) / m) ^ m * ((m : ℝ) ^ m / m.factorial) := by
    rw [← mul_div_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ _ hm0.ne']
  have h4 : (1 + (M : ℝ) / m) ^ m ≤ (1 + K / m) ^ m :=
    pow_le_pow_left₀ (by positivity) (add_le_add_left (div_le_div_of_nonneg_right hMK hm0.le) 1) m
  have hC : ((M + m).choose m : ℝ) ≤ (1 + K / m) ^ m * Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    calc ((M + m).choose m : ℝ) ≤ ((M : ℝ) + m) ^ m / m.factorial := h1
      _ = (1 + (M : ℝ) / m) ^ m * ((m : ℝ) ^ m / m.factorial) := h3
      _ ≤ (1 + K / m) ^ m * Real.exp m := mul_le_mul h4 h2 (by positivity) (by positivity)
  have hce : 1 ≤ c * Real.exp 1 := by
    have := Real.add_one_le_exp 1
    nlinarith
  calc c ^ m * ((M + m).choose m : ℝ) ≤ c ^ m * ((1 + K / m) ^ m * Real.exp 1 ^ m) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (c * Real.exp 1) ^ (m : ℝ) * (1 + K / m) ^ (m : ℝ) := by
        rw [Real.rpow_natCast, Real.rpow_natCast, mul_pow]
        ring
    _ ≤ (c * Real.exp 1) ^ y * (1 + K / y) ^ y :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hce hmy) (one_add_div_rpow_le hK hm0 hmy)
          (by positivity) (by positivity)
    _ = (c * Real.exp 1 * (1 + K / y)) ^ y := (Real.mul_rpow (by positivity) (by positivity)).symm

theorem rhoR_nonneg {r : ℝ} (hr : 1 < r) {α : ℝ} (hα : 0 < α) : 0 ≤ rhoR r α := by
  have hr1 : 0 < r - 1 := by linarith
  exact mul_nonneg (div_nonneg (by linarith) (by positivity))
    (Real.rpow_nonneg (by have := div_pos (mul_pos hα (by linarith : (0 : ℝ) < r)) hr1
                          positivity) _)

theorem rhoR_pow {r : ℝ} (hr : 1 < r) {α : ℝ} (hα : 0 < α) (k : ℕ) :
    rhoR r α ^ k = (4 * (r - 1) / r ^ 2) ^ k *
      (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ ((k : ℝ) / α) := by
  have hr1 : 0 < r - 1 := by linarith
  have hQ : 0 ≤ 2 * r * Real.exp 1 * (α * r / (r - 1) + 1) := by
    have := div_pos (mul_pos hα (by linarith : (0 : ℝ) < r)) hr1
    positivity
  rw [rhoR, mul_pow, ← Real.rpow_natCast ((2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ (1 / α)) k,
    ← Real.rpow_mul hQ, one_div_mul_eq_div]

end CoefficientMass
