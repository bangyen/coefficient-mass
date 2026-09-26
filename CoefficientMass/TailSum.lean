/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleBeta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Tail Sum as an Integral

This module proves the second step of Lemma 4.11 of `coefficient-mass.tex`:
`∑_{s > N} C(s - 1, N) 2^{-s} ∫_0^1 t^ℓ (1 - t)^{s - m - 1} dt
= ∫_0^1 t^ℓ (1 - t)^q (1 + t)^{-(N + 1)} dt` for `N = m + q`.  The terms are
nonnegative and continuous on `[0, 1]`, the inner sum is
`∑_s C(s - 1, N) y^s = (y / (1 - y))^{N + 1}` at `y = (1 - t) / 2`, and dominated
convergence exchanges the sum and the integral.

## Definitions

* `tailTerm`.

## Theorems

* `tailTerm_nonneg`.
* `hasSum_tailTerm`.
* `hasSum_tail_betaI`.
-/

open intervalIntegral MeasureTheory

namespace CoefficientMass

/-- `C(t + N, N) 2^{-(t + N + 1)} x^ℓ (1 - x)^{t + q}`. -/
noncomputable def tailTerm (ℓ q N t : ℕ) (x : ℝ) : ℝ :=
  ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) * (x ^ ℓ * (1 - x) ^ (t + q))

theorem tailTerm_nonneg (ℓ q N t : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ tailTerm ℓ q N t x :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (mul_nonneg (pow_nonneg hx0 _) (pow_nonneg (by linarith) _))

theorem hasSum_tailTerm (ℓ q N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun t => tailTerm ℓ q N t x) (x ^ ℓ * (1 - x) ^ q / (1 + x) ^ (N + 1)) := by
  have hr : ‖(1 - x) / 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one N hr).mul_left
    ((1 / 2 : ℝ) ^ (N + 1) * x ^ ℓ * (1 - x) ^ q)
  have h3 : (1 / 2 : ℝ) ^ (N + 1) * 2 ^ (N + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  convert h using 1
  · funext t
    rw [tailTerm, div_eq_mul_one_div (1 - x) 2, mul_pow]
    ring
  · rw [show (1 : ℝ) - (1 - x) / 2 = (1 + x) / 2 by ring, div_pow (1 + x) 2 (N + 1),
      one_div_div ((1 + x) ^ (N + 1)) (2 ^ (N + 1)),
      show (1 / 2 : ℝ) ^ (N + 1) * x ^ ℓ * (1 - x) ^ q * (2 ^ (N + 1) / (1 + x) ^ (N + 1)) =
        x ^ ℓ * (1 - x) ^ q * ((1 / 2) ^ (N + 1) * 2 ^ (N + 1)) / (1 + x) ^ (N + 1) by ring,
      h3, mul_one]

/-- `∑_t C(t + N, N) 2^{-(t + N + 1)} B(ℓ + 1, t + q + 1) = ∫_0^1 x^ℓ (1 - x)^q / (1 + x)^{N+1}`. -/
theorem hasSum_tail_betaI (ℓ q N : ℕ) :
    HasSum (fun t : ℕ => ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) * betaI ℓ (t + q))
      (∫ x in (0 : ℝ)..1, x ^ ℓ * (1 - x) ^ q / (1 + x) ^ (N + 1)) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ ℓ * (1 - x) ^ q / (1 + x) ^ (N + 1))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact pow_ne_zero _ (by linarith [hx.1])
  have hmem : ∀ x ∈ Set.uIoc (0 : ℝ) 1, 0 ≤ x ∧ x ≤ 1 := fun x hx => by
    rw [Set.uIoc_of_le zero_le_one] at hx
    exact ⟨hx.1.le, hx.2⟩
  have hmeas : ∀ t, AEStronglyMeasurable (tailTerm ℓ q N t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := fun t =>
    (by fun_prop : Continuous fun x : ℝ => ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) *
      (x ^ ℓ * (1 - x) ^ (t + q))).aestronglyMeasurable
  have hbound : ∀ t, ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖tailTerm ℓ q N t x‖ ≤ ‖tailTerm ℓ q N t x‖ := fun t => ae_of_all _ fun _ _ => le_rfl
  have hsumm : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Summable fun t => ‖tailTerm ℓ q N t x‖ := ae_of_all _ fun x hx => by
    obtain ⟨h0, h1⟩ := hmem x hx
    exact (hasSum_tailTerm ℓ q N h0 h1).summable.congr fun t =>
      (Real.norm_of_nonneg (tailTerm_nonneg ℓ q N t h0 h1)).symm
  have hint : IntervalIntegrable (fun x => ∑' t, ‖tailTerm ℓ q N t x‖) volume 0 1 := by
    refine (hcont.congr fun x hx => ?_).intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [tsum_congr fun t => Real.norm_of_nonneg (tailTerm_nonneg ℓ q N t hx.1 hx.2)]
    exact (hasSum_tailTerm ℓ q N hx.1 hx.2).tsum_eq
  have hlim : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      HasSum (fun t => tailTerm ℓ q N t x) (x ^ ℓ * (1 - x) ^ q / (1 + x) ^ (N + 1)) :=
    ae_of_all _ fun x hx => hasSum_tailTerm ℓ q N (hmem x hx).1 (hmem x hx).2
  have key := hasSum_integral_of_dominated_convergence (fun t x => ‖tailTerm ℓ q N t x‖)
    hmeas hbound hsumm hint hlim
  convert key using 1
  funext t
  rw [betaI, ← intervalIntegral.integral_const_mul]
  rfl

end CoefficientMass
