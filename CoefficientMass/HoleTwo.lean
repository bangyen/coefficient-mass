/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleInt

/-!
# Two Holes

This module proves Lemma 4.8 of `coefficient-mass.tex`:
`Φ({1, …, b + q} \ {3, b}) ≤ 1 / (q + 1)` for `b ≥ 4`.  By Lemma 4.7 the left
side is `∫_0^1 v^q M(v) dv` with
`M = (3b / (b - 3)) (2^{-b} ((1 + v)^{b - 1} + (1 - v)^{b - 1}) - v^{b - 2} / 2)`.
For `b = 4`, `M = (3/2)(1 - v^2)`.  For `b ≥ 5`, the Bernstein expansion of
`M` has coefficients in `[0, 1]`, so `M ≤ 1` on `[0, 1]`.

## Theorems

* `twoHole_weight_le`.
* `twoHole_integrand`.
* `confTail_two_holes`.
-/

open intervalIntegral

namespace CoefficientMass

/-- For `b = p + 5`, `M(v) ≤ 1` on `[0, 1]`. -/
theorem twoHole_weight_le (p : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (3 * ((p + 5 : ℕ) : ℝ) / (((p + 5 : ℕ) : ℝ) - 3)) * ((1 / 2) ^ (p + 5) * ((1 + v) ^ (p + 4) +
      (1 - v) ^ (p + 4)) - v ^ (p + 3) / 2) ≤ 1 := by
  rw [show (((p + 5 : ℕ) : ℝ) - 3) = (p : ℝ) + 2 by push_cast; ring, Nat.cast_add,
    Nat.cast_ofNat]
  set w := 1 - v with hw
  have hw0 : 0 ≤ w := by linarith
  set B : ℕ → ℝ := fun i => v ^ i * w ^ (p + 4 - i) * ((p + 4).choose i : ℝ) with hB
  have hB0 : ∀ i, 0 ≤ B i := fun i => by positivity
  have h1 : ∑ i ∈ Finset.range (p + 3), B i + B (p + 3) + B (p + 4) = 1 := by
    rw [← Finset.sum_range_succ, ← Finset.sum_range_succ, hB, ← add_pow,
      show v + w = 1 by ring, one_pow]
  have h2 : (1 + v) ^ (p + 4) = ∑ i ∈ Finset.range (p + 3), 2 ^ i * B i +
      2 ^ (p + 3) * B (p + 3) + 2 ^ (p + 4) * B (p + 4) := by
    rw [← Finset.sum_range_succ (fun i => 2 ^ i * B i),
      ← Finset.sum_range_succ (fun i => 2 ^ i * B i), show 1 + v = 2 * v + w by ring, add_pow]
    exact Finset.sum_congr rfl fun i _ => by rw [hB, mul_pow]; ring
  have h3 : (1 - v) ^ (p + 4) = B 0 := by
    rw [hB, pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
  have hc : ((p + 4).choose (p + 3) : ℝ) = p + 4 := by
    rw [show p + 4 = p + 3 + 1 from rfl, Nat.choose_succ_self_right]
    push_cast
    ring
  have h4 : B (p + 4) = v ^ (p + 4) := by
    rw [hB, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
  set u := v ^ (p + 3) * w with hu
  have h5 : B (p + 3) = ((p : ℝ) + 4) * u := by
    rw [hB, hu, show p + 4 - (p + 3) = 1 by omega, pow_one, hc]
    ring
  have hu0 : 0 ≤ u := by positivity
  have h6 : v ^ (p + 3) = B (p + 4) + u := by rw [h4, hu, hw]; ring
  -- the low coefficients
  have hT : ∑ i ∈ Finset.range (p + 3), 2 ^ i * B i + B 0 ≤
      2 ^ (p + 2) * ∑ i ∈ Finset.range (p + 3), B i := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => B i), mul_add, Finset.mul_sum,
      pow_zero, one_mul]
    have : ∀ i ∈ Finset.range (p + 2), 2 ^ (i + 1) * B (i + 1) ≤ 2 ^ (p + 2) * B (i + 1) :=
      fun i hi => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num)
        (by have := Finset.mem_range.1 hi; omega)) (hB0 _)
    have h2p : (2 : ℝ) ≤ 2 ^ (p + 2) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [Finset.sum_le_sum this, hB0 0]
  have hr : (1 / 2 : ℝ) ^ (p + 5) * 2 ^ (p + 2) = 1 / 8 := by
    rw [show p + 5 = p + 2 + 3 by ring, pow_add, mul_right_comm, ← mul_pow]
    norm_num
  have hr3 : (1 / 2 : ℝ) ^ (p + 5) * 2 ^ (p + 3) = 1 / 4 := by
    rw [show p + 5 = p + 3 + 2 by ring, pow_add, mul_right_comm, ← mul_pow]
    norm_num
  have hr4 : (1 / 2 : ℝ) ^ (p + 5) * 2 ^ (p + 4) = 1 / 2 := by
    rw [show p + 5 = p + 4 + 1 by ring, pow_add, mul_right_comm, ← mul_pow]
    norm_num
  set S := ∑ i ∈ Finset.range (p + 3), B i
  set T := ∑ i ∈ Finset.range (p + 3), 2 ^ i * B i
  have hX : (1 / 2) ^ (p + 5) * ((1 + v) ^ (p + 4) + (1 - v) ^ (p + 4)) - v ^ (p + 3) / 2 =
      (1 / 2) ^ (p + 5) * (T + B 0) + ((p : ℝ) + 2) * u / 4 := by
    rw [h2, h3, h6, h5]
    linear_combination (((p : ℝ) + 4) * u) * hr3 + B (p + 4) * hr4
  have hS : (1 / 2 : ℝ) ^ (p + 5) * (T + B 0) ≤ S / 8 := by
    have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (p + 5))
    nlinarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hB0 i
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [hX, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [mul_nonneg hp hS0, mul_nonneg (mul_nonneg hp hp) hu0, mul_nonneg hp hu0,
    hB0 (p + 4), h1, h5]

/-- The weights of the two holes `{3, b}`, `π_3 = -3b / (b - 3)` and `π_b = 3b / (b - 3)`. -/
theorem twoHole_integrand {b : ℕ} (hb : 4 ≤ b) :
    holeWeight {3, b} 3 = -(3 * (b : ℝ) / ((b : ℝ) - 3)) ∧
      holeWeight {3, b} b = 3 * (b : ℝ) / ((b : ℝ) - 3) := by
  have h3b : (3 : ℕ) ≠ b := by omega
  constructor
  · rw [holeWeight, Finset.prod_pair h3b, Finset.erase_insert (by rw [Finset.mem_singleton]; omega),
      Finset.prod_singleton, Nat.cast_ofNat, show (3 : ℝ) - b = -(b - 3) by ring, div_neg]
  · rw [holeWeight, Finset.prod_pair h3b, Finset.erase_insert_of_ne h3b, Finset.erase_singleton,
      Finset.insert_empty, Finset.prod_singleton, Nat.cast_ofNat]

/-- Lemma 4.8 (two holes). -/
theorem confTail_two_holes {b q : ℕ} (hb : 4 ≤ b) :
    confTail (Finset.Icc 1 (b + q) \ {3, b}) ≤ 1 / ((q : ℝ) + 1) := by
  have h3b : (3 : ℕ) ≠ b := by omega
  have hK : 0 < 3 * (b : ℝ) / ((b : ℝ) - 3) := by
    have : (4 : ℝ) ≤ b := by exact_mod_cast hb
    exact div_pos (by linarith) (by linarith)
  obtain ⟨hw3, hwb⟩ := twoHole_integrand hb
  rw [holeIntegral (b + q) {3, b} (Finset.insert_nonempty _ _) (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega) fun c hc => by
      rcases Finset.mem_insert.1 hc with rfl | hc
      · omega
      · rw [Finset.mem_singleton.1 hc]
        omega]
  have hqi : ∫ v in (0 : ℝ)..1, v ^ q = 1 / ((q : ℝ) + 1) := by
    rw [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero q), sub_zero]
  rcases Nat.lt_or_ge b 5 with h5 | h5
  · obtain rfl : b = 4 := by omega
    have hi1 := (by fun_prop : Continuous fun v : ℝ => 3 / 2 * v ^ q).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
    have hi2 := (by fun_prop : Continuous fun v : ℝ => 3 / 2 * v ^ (q + 2)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
    rw [integral_congr (g := fun v : ℝ => 3 / 2 * v ^ q - 3 / 2 * v ^ (q + 2)) fun v _ => by
      rw [Finset.sum_pair h3b, hw3, hwb, abs_neg, abs_of_pos hK,
        show 4 + q - 3 = q + 1 by omega, show 4 + q - 4 = q by omega,
        show ((4 : ℕ) : ℝ) = 4 by norm_num, show (3 : ℕ) - 1 = 2 from rfl,
        show (4 : ℕ) - 1 = 3 from rfl]
      ring, integral_sub hi1 hi2, integral_const_mul, integral_const_mul, hqi, integral_pow,
      one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    have hy : 1 / ((q : ℝ) + 1) ≤ 3 * (1 / (((q + 2 : ℕ) : ℝ) + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      linarith
    linarith
  · obtain ⟨p, rfl⟩ : ∃ p, b = p + 5 := ⟨b - 5, by omega⟩
    rw [← hqi]
    refine integral_mono_on zero_le_one (by fun_prop : Continuous fun v : ℝ =>
      ∑ c ∈ ({3, p + 5} : Finset ℕ), (1 / 2) ^ c * v ^ (p + 5 + q - c) *
        (holeWeight {3, p + 5} c * (1 + v) ^ (c - 1) +
          |holeWeight {3, p + 5} c| * (1 - v) ^ (c - 1))).intervalIntegrable 0 1
      (by fun_prop : Continuous fun v : ℝ => v ^ q).intervalIntegrable 0 1 fun v hv => ?_
    obtain ⟨hv0, hv1⟩ := hv
    rw [Finset.sum_pair h3b, hw3, hwb, abs_neg, abs_of_pos hK,
      show p + 5 + q - 3 = q + (p + 2) by omega, show p + 5 + q - (p + 5) = q by omega,
      show p + 5 - 1 = p + 4 by omega, show (3 : ℕ) - 1 = 2 from rfl]
    have hM := twoHole_weight_le p hv0 hv1
    have hq : 0 ≤ v ^ q := pow_nonneg hv0 q
    calc _ = v ^ q * ((3 * ((p + 5 : ℕ) : ℝ) / (((p + 5 : ℕ) : ℝ) - 3)) *
          ((1 / 2) ^ (p + 5) * ((1 + v) ^ (p + 4) + (1 - v) ^ (p + 4)) - v ^ (p + 3) / 2)) := by
          ring
      _ ≤ v ^ q * 1 := mul_le_mul_of_nonneg_left hM hq
      _ = v ^ q := mul_one _

end CoefficientMass
