/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Exponential Bound in the Tail

This module proves the pointwise bound of Lemma 4.11 of `coefficient-mass.tex`:
`(q + 1) t (1 - t)^q ≤ e^{-1} (1 + t)^q` for `0 ≤ t ≤ 1` and `q ≥ 1`.  The series of
`log (1 + t) - log (1 - t)` gives `(1 - t) / (1 + t) ≤ e^{-2t}`, and
`(q + 1) t e^{-2qt} ≤ 2qt e^{-2qt} ≤ 1/e` since `y e^{-y} ≤ 1/e`.

## Theorems

* `one_sub_div_one_add_le_exp`.
* `mul_exp_neg_le`.
* `tail_weight_le`.
-/

namespace CoefficientMass

theorem one_sub_div_one_add_le_exp {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) / (1 + t) ≤ Real.exp (-2 * t) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (abs_lt.2 ⟨by linarith, ht1⟩)
  have h2 := le_hasSum h 0 fun j _ => mul_nonneg (by positivity) (pow_nonneg ht0 _)
  norm_num at h2
  have hpos : 0 < (1 - t) / (1 + t) := div_pos (by linarith) (by linarith)
  rw [← Real.exp_log hpos, Real.exp_le_exp, Real.log_div (by linarith) (by linarith)]
  linarith

/-- `y e^{-y} ≤ e^{-1}`. -/
theorem mul_exp_neg_le (y : ℝ) : y * Real.exp (-y) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y - 1)
  calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- `(q + 1) t (1 - t)^q ≤ e^{-1} (1 + t)^q` on `[0, 1]` for `q ≥ 1`. -/
theorem tail_weight_le {t : ℝ} {q : ℕ} (hq : 1 ≤ q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((q : ℝ) + 1) * t * (1 - t) ^ q ≤ Real.exp (-1) * (1 + t) ^ q := by
  rcases eq_or_lt_of_le ht1 with rfl | ht1
  · rw [sub_self, zero_pow (by omega), mul_zero]
    positivity
  have hy0 : 0 ≤ (1 - t) / (1 + t) := div_nonneg (by linarith) (by linarith)
  have hyq : ((1 - t) / (1 + t)) ^ q ≤ Real.exp (-(2 * q * t)) := by
    calc ((1 - t) / (1 + t)) ^ q ≤ Real.exp (-2 * t) ^ q :=
          pow_le_pow_left₀ hy0 (one_sub_div_one_add_le_exp ht0 ht1) q
      _ = Real.exp (-(2 * q * t)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : ((q : ℝ) + 1) * t ≤ 2 * q * t := by nlinarith
  have h2 : ((q : ℝ) + 1) * t * ((1 - t) / (1 + t)) ^ q ≤ Real.exp (-1) :=
    (mul_le_mul h1 hyq (pow_nonneg hy0 q) (by positivity)).trans (mul_exp_neg_le _)
  have e : (1 - t) ^ q = ((1 - t) / (1 + t)) ^ q * (1 + t) ^ q := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (by linarith))]
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg (by linarith) q)

end CoefficientMass
