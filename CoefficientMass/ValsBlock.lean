/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleBeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Block of Kept Holes

This module proves the last step of Lemma 4.10 of `coefficient-mass.tex`.  For the
block `C° = {ℓ + 1, …, 2ℓ + 1}` the values at the holes sum to `∫_0^1 v^q G(v) dv`
with `G = ∑_r 2^{-(ℓ+1+r)} (2ℓ+1)! / (ℓ! r! (ℓ-r)!) v^{ℓ-r} (1 - v)^{ℓ+r}`, and the
binomial theorem gives `G = (2ℓ+1)! / (ℓ!^2 2^{2ℓ+1}) (1 - v^2)^ℓ`.  With Wallis'
`∫_0^1 (1 - v^2)^ℓ dv = 4^ℓ ℓ!^2 / (2ℓ+1)!`, `∫_0^1 G = 1/2`; `G` is nonincreasing and
`v^q` nondecreasing, so Chebyshev's integral inequality bounds the sum by `1 / (2(q + 1))`.

## Definitions

* `wallisI`.
* `blockCoef`.

## Theorems

* `wallisI_succ`.
* `wallisI_eq`.
* `integral_pow_mul_le`.
* `blockCoef_sum_eq`.
* `block_le`.
-/

open intervalIntegral

namespace CoefficientMass

/-- `∫_0^1 (1 - v^2)^ℓ dv`. -/
noncomputable def wallisI (ℓ : ℕ) : ℝ :=
  ∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ ℓ

/-- `2^{-(ℓ+1+r)} (2ℓ+1)! / (ℓ! r! (ℓ-r)!)`. -/
noncomputable def blockCoef (ℓ r : ℕ) : ℝ :=
  (1 / 2) ^ (ℓ + 1 + r) * ((2 * ℓ + 1).factorial /
    (ℓ.factorial * r.factorial * (ℓ - r).factorial) : ℝ)

theorem wallisI_succ (ℓ : ℕ) : (2 * (ℓ : ℝ) + 3) * wallisI (ℓ + 1) = (2 * ℓ + 2) * wallisI ℓ := by
  have hderiv : ∀ v ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => v * (1 - v ^ 2) ^ (ℓ + 1))
      ((2 * (ℓ : ℝ) + 3) * (1 - v ^ 2) ^ (ℓ + 1) - (2 * ℓ + 2) * (1 - v ^ 2) ^ ℓ) v := by
    intro v _
    have h := (hasDerivAt_id' v).mul (((hasDerivAt_pow 2 v).const_sub 1).fun_pow (ℓ + 1))
    convert h using 1
    rw [Nat.add_sub_cancel, show 2 - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hi1 := (by fun_prop : Continuous fun v : ℝ => (2 * (ℓ : ℝ) + 3) * (1 - v ^ 2) ^ (ℓ + 1))
    |>.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hi2 := (by fun_prop : Continuous fun v : ℝ => (2 * (ℓ : ℝ) + 2) * (1 - v ^ 2) ^ ℓ)
    |>.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have h := integral_eq_sub_of_hasDerivAt hderiv (hi1.sub hi2)
  rw [integral_sub hi1 hi2, integral_const_mul, integral_const_mul] at h
  rw [wallisI, wallisI]
  norm_num at h
  linarith

/-- Wallis: `∫_0^1 (1 - v^2)^ℓ dv = 4^ℓ ℓ!^2 / (2ℓ + 1)!`. -/
theorem wallisI_eq (ℓ : ℕ) :
    wallisI ℓ = 4 ^ ℓ * (ℓ.factorial : ℝ) ^ 2 / (2 * ℓ + 1).factorial := by
  induction ℓ with
  | zero =>
    rw [wallisI]
    simp only [pow_zero, integral_const, sub_zero, smul_eq_mul, mul_one, Nat.factorial_zero,
      Nat.cast_one, one_pow, Nat.mul_zero, Nat.zero_add, Nat.factorial_one, div_one]
  | succ ℓ ih =>
    have h := wallisI_succ ℓ
    rw [ih] at h
    rw [eq_div_iff (by positivity), show 2 * (ℓ + 1) + 1 = 2 * ℓ + 1 + 1 + 1 by ring,
      Nat.factorial_succ (2 * ℓ + 1 + 1), Nat.factorial_succ (2 * ℓ + 1), Nat.factorial_succ ℓ]
    have hf : ((2 * ℓ + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp at h
    push_cast
    linear_combination (2 * (ℓ : ℝ) + 2) * h

/-- Chebyshev: for `G` nonincreasing on `[0, 1]`, `∫_0^1 v^q G ≤ (1 / (q + 1)) ∫_0^1 G`. -/
theorem integral_pow_mul_le {G : ℝ → ℝ} (hG : ContinuousOn G (Set.uIcc 0 1))
    (hanti : AntitoneOn G (Set.Icc 0 1)) {q : ℕ} (hq : 1 ≤ q) :
    ∫ v in (0 : ℝ)..1, v ^ q * G v ≤ 1 / ((q : ℝ) + 1) * ∫ v in (0 : ℝ)..1, G v := by
  set c : ℝ := 1 / ((q : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  set v0 : ℝ := c ^ ((q : ℝ)⁻¹) with hv0
  have hv0q : v0 ^ q = c := Real.rpow_inv_natCast_pow hc0 (by omega)
  have hv00 : 0 ≤ v0 := Real.rpow_nonneg hc0 _
  have hv01 : v0 ≤ 1 := Real.rpow_le_one hc0 hc1 (by positivity)
  have hGi : IntervalIntegrable G MeasureTheory.volume 0 1 := hG.intervalIntegrable
  have hpt : ∀ v ∈ Set.Icc (0 : ℝ) 1, (v ^ q - c) * (G v - G v0) ≤ 0 := fun v hv => by
    rcases le_total v v0 with h | h
    · have h1 : v ^ q ≤ c := hv0q ▸ pow_le_pow_left₀ hv.1 h q
      have h2 : G v0 ≤ G v := hanti hv ⟨hv00, hv01⟩ h
      nlinarith
    · have h1 : c ≤ v ^ q := hv0q ▸ pow_le_pow_left₀ hv00 h q
      have h2 : G v ≤ G v0 := hanti ⟨hv00, hv01⟩ hv h
      nlinarith
  have hi1 : IntervalIntegrable (fun v : ℝ => v ^ q * G v) MeasureTheory.volume 0 1 :=
    ((by fun_prop : Continuous fun v : ℝ => v ^ q).continuousOn.mul hG).intervalIntegrable
  have hi2 : IntervalIntegrable (fun v : ℝ => c * G v) MeasureTheory.volume 0 1 :=
    hGi.const_mul c
  have hi3 : IntervalIntegrable (fun v : ℝ => G v0 * v ^ q - c * G v0) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun v : ℝ => G v0 * v ^ q - c * G v0).intervalIntegrable 0 1
  have hle := integral_mono_on zero_le_one ((hi1.sub hi2).sub hi3)
    (intervalIntegral.intervalIntegrable_const (c := (0 : ℝ))) fun v hv => by
      have := hpt v hv
      nlinarith
  rw [integral_sub (hi1.sub hi2) hi3, integral_sub hi1 hi2, integral_const_mul,
    integral_sub ((by fun_prop : Continuous fun v : ℝ => G v0 * v ^ q).intervalIntegrable 0 1)
      intervalIntegral.intervalIntegrable_const, integral_const_mul, integral_pow,
    integral_const] at hle
  rw [hc] at hle ⊢
  norm_num at hle ⊢
  linarith

/-- `∑_r 2^{-(ℓ+1+r)} (2ℓ+1)! / (ℓ! r! (ℓ-r)!) v^{ℓ-r} (1-v)^{ℓ+r} = (2ℓ+1)! / (ℓ!^2 2^{2ℓ+1})
(1 - v^2)^ℓ`, from the binomial theorem. -/
theorem blockCoef_sum_eq (ℓ : ℕ) (v : ℝ) :
    ∑ r ∈ Finset.range (ℓ + 1), blockCoef ℓ r * (v ^ (ℓ - r) * (1 - v) ^ (ℓ + r)) =
      (2 * ℓ + 1).factorial / (ℓ.factorial : ℝ) ^ 2 * (1 / 2) ^ (2 * ℓ + 1) *
        (1 - v ^ 2) ^ ℓ := by
  have e : (1 / 2 : ℝ) ^ (2 * ℓ + 1) * (1 - v ^ 2) ^ ℓ =
      (1 / 2) ^ (ℓ + 1) * ((1 - v) ^ ℓ * ((1 - v) / 2 + v) ^ ℓ) := by
    rw [← mul_pow, show (1 - v) * ((1 - v) / 2 + v) = 1 / 2 * (1 - v ^ 2) by ring, mul_pow]
    ring
  rw [mul_assoc, e, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr := Finset.mem_range.1 hr
  rw [Nat.cast_choose ℝ (by omega : r ≤ ℓ), blockCoef, div_eq_mul_one_div (1 - v) 2, mul_pow]
  have h1 : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((ℓ - r).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Lemma 4.10 for the block: `∑_r blockCoef ℓ r · B(ℓ - r + q + 1, ℓ + r + 1) ≤ 1 / (2(q + 1))`. -/
theorem block_le (ℓ : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    ∑ r ∈ Finset.range (ℓ + 1), blockCoef ℓ r * betaI (ℓ - r + q) (ℓ + r) ≤
      1 / (2 * ((q : ℝ) + 1)) := by
  set K : ℝ := (2 * ℓ + 1).factorial / (ℓ.factorial : ℝ) ^ 2 * (1 / 2) ^ (2 * ℓ + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : ∑ r ∈ Finset.range (ℓ + 1), blockCoef ℓ r * betaI (ℓ - r + q) (ℓ + r) =
      ∫ v in (0 : ℝ)..1, v ^ q * (K * (1 - v ^ 2) ^ ℓ) := by
    rw [integral_congr (g := fun v : ℝ => ∑ r ∈ Finset.range (ℓ + 1),
      blockCoef ℓ r * (v ^ (ℓ - r + q) * (1 - v) ^ (ℓ + r))) fun v _ => by
        rw [hK, ← blockCoef_sum_eq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring,
      integral_finset_sum fun r _ => (by fun_prop : Continuous fun v : ℝ =>
        blockCoef ℓ r * (v ^ (ℓ - r + q) * (1 - v) ^ (ℓ + r))).intervalIntegrable 0 1]
    exact Finset.sum_congr rfl fun r _ => by rw [integral_const_mul, betaI]
  have hanti : AntitoneOn (fun v : ℝ => K * (1 - v ^ 2) ^ ℓ) (Set.Icc 0 1) :=
    fun a ha b hb hab => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by nlinarith [hb.2, hb.1])
      (by nlinarith [ha.1]) ℓ) hK0
  have hcheb := integral_pow_mul_le (G := fun v : ℝ => K * (1 - v ^ 2) ^ ℓ)
    (by fun_prop : Continuous fun v : ℝ => K * (1 - v ^ 2) ^ ℓ).continuousOn hanti hq
  have hG : ∫ v in (0 : ℝ)..1, K * (1 - v ^ 2) ^ ℓ = 1 / 2 := by
    rw [integral_const_mul, ← wallisI, wallisI_eq, hK]
    have h4 : (1 / 2 : ℝ) ^ (2 * ℓ + 1) * 4 ^ ℓ = 1 / 2 := by
      rw [pow_succ, pow_mul, mul_right_comm, ← mul_pow]
      norm_num
    calc _ = ((1 / 2 : ℝ) ^ (2 * ℓ + 1) * 4 ^ ℓ) * (((2 * ℓ + 1).factorial /
          (ℓ.factorial : ℝ) ^ 2) * ((ℓ.factorial : ℝ) ^ 2 / (2 * ℓ + 1).factorial)) := by ring
      _ = 1 / 2 := by
        rw [h4, div_mul_div_comm, mul_comm ((ℓ.factorial : ℝ) ^ 2), div_self (by positivity),
          mul_one]
  rw [hsum]
  calc _ ≤ 1 / ((q : ℝ) + 1) * ∫ v in (0 : ℝ)..1, K * (1 - v ^ 2) ^ ℓ := hcheb
    _ = 1 / (2 * ((q : ℝ) + 1)) := by rw [hG, one_div_mul_one_div, mul_comm]

end CoefficientMass
