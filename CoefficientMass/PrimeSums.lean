/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Weighted Logarithmic Sums

This module estimates the sums of Corollaries 3.5 and 3.6 of `coefficient-mass.tex`:
`∑_{k ≤ L} k log k` and `∑_{k ≤ L} k log log k` are within `O(L^2)` of
`(L(L + 1)/2) log L` and `(L(L + 1)/2) log log L`.  Since `log y ≤ y / e`, each deficit
`k log (L/k)` is at most `L/e`, and `k (log log L - log log k) ≤ k log (L/k) / log 2`.

## Theorems

* `sum_range_succ_eq`.
* `mul_log_div_le`.
* `sum_mul_log_ge`.
* `sum_mul_log_le`.
* `log_log_sub_le`.
* `sum_mul_log_log_ge`.
* `sum_mul_log_log_le`.
-/

namespace CoefficientMass

theorem sum_range_succ_eq : ∀ L : ℕ, ∑ i ∈ Finset.range L, ((i : ℝ) + 1) = L * (L + 1) / 2 := by
  intro L
  induction L with
  | zero => rw [Finset.sum_range_zero]; push_cast; ring
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `x log (L / x) ≤ L / e` for `x, L > 0`. -/
theorem mul_log_div_le {x L : ℝ} (hx : 0 < x) (hL : 0 < L) :
    x * Real.log (L / x) ≤ L / Real.exp 1 := by
  have hy : 0 < L / x / Real.exp 1 := by positivity
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at h
  have h' : Real.log (L / x) ≤ L / x / Real.exp 1 := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  calc x * Real.log (L / x) ≤ x * (L / x / Real.exp 1) := mul_le_mul_of_nonneg_left h' hx.le
    _ = L / Real.exp 1 := by field_simp

/-- `∑_{k ≤ L} k log k ≥ (L(L + 1)/2) log L - L^2 / e`. -/
theorem sum_mul_log_ge {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) * (L + 1) / 2 * Real.log L - (L : ℝ) ^ 2 / Real.exp 1 ≤
      ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hterm : ∀ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log L - L / Real.exp 1 ≤
      ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) := fun i _ => by
    have h := mul_log_div_le (show (0 : ℝ) < (i : ℝ) + 1 by positivity) hL0
    rw [Real.log_div hL0.ne' (by positivity)] at h
    linarith
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_range_succ_eq, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at this
  calc (L : ℝ) * (L + 1) / 2 * Real.log L - (L : ℝ) ^ 2 / Real.exp 1
      = (L : ℝ) * (L + 1) / 2 * Real.log L - L * (L / Real.exp 1) := by ring
    _ ≤ _ := this

/-- `∑_{k ≤ L} k log k ≤ (L(L + 1)/2) log L`. -/
theorem sum_mul_log_le (L : ℕ) :
    ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) ≤
      (L : ℝ) * (L + 1) / 2 * Real.log L := by
  rw [← sum_range_succ_eq, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (by
      have := Finset.mem_range.1 hi
      exact_mod_cast (show i + 1 ≤ L by omega))) (by positivity)

/-- `log log L - log log k ≤ log (L / k) / log 2` for `2 ≤ k ≤ L`. -/
theorem log_log_sub_le {k L : ℝ} (hk : 2 ≤ k) (hkL : k ≤ L) :
    Real.log (Real.log L) - Real.log (Real.log k) ≤ Real.log (L / k) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk
  have hlk0 : 0 < Real.log k := by linarith
  have hlL : Real.log k ≤ Real.log L := Real.log_le_log (by linarith) hkL
  have hdiv : Real.log (L / k) = Real.log L - Real.log k :=
    Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hlk0' : Real.log k ≠ 0 := hlk0.ne'
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log L / Real.log k by
    exact div_pos (by linarith) hlk0)
  rw [Real.log_div (ne_of_gt (by linarith)) hlk0'] at h1
  have h2 : Real.log L / Real.log k - 1 = (Real.log L - Real.log k) / Real.log k := by
    field_simp
  rw [h2, ← hdiv] at h1
  have h3 : Real.log (L / k) / Real.log k ≤ Real.log (L / k) / Real.log 2 :=
    div_le_div_of_nonneg_left (by rw [hdiv]; linarith) hl2 hlk
  linarith

/-- `∑_{k ≤ L} k log log k ≥ (L(L + 1)/2) log log L - L^2 / (e log 2) - log log L`. -/
theorem sum_mul_log_log_ge {L : ℕ} (hL : 2 ≤ L) :
    (L : ℝ) * (L + 1) / 2 * Real.log (Real.log L) - (L : ℝ) ^ 2 / (Real.exp 1 * Real.log 2) -
        Real.log (Real.log L) ≤
      ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (Real.log ((i : ℝ) + 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (Real.log L) -
      L / (Real.exp 1 * Real.log 2) - (if i = 0 then Real.log (Real.log L) else 0) ≤
      ((i : ℝ) + 1) * Real.log (Real.log ((i : ℝ) + 1)) := fun i hi => by
    have hiL := Finset.mem_range.1 hi
    have hpos : 0 ≤ L / (Real.exp 1 * Real.log 2) := by positivity
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [if_pos rfl]
      simp only [Nat.cast_zero, zero_add, one_mul, Real.log_one, Real.log_zero]
      linarith
    · rw [if_neg (by omega), sub_zero]
      have hk : (2 : ℝ) ≤ (i : ℝ) + 1 := by
        have : (1 : ℝ) ≤ i := by exact_mod_cast h0
        linarith
      have hkL : (i : ℝ) + 1 ≤ L := by exact_mod_cast (show i + 1 ≤ L by omega)
      have h1 := log_log_sub_le hk hkL
      have h2 := mul_log_div_le (show (0 : ℝ) < (i : ℝ) + 1 by positivity) hL0
      have h3 : ((i : ℝ) + 1) * (Real.log (Real.log L) - Real.log (Real.log ((i : ℝ) + 1))) ≤
          ((i : ℝ) + 1) * (Real.log (L / ((i : ℝ) + 1)) / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : ((i : ℝ) + 1) * (Real.log (L / ((i : ℝ) + 1)) / Real.log 2) ≤
          L / (Real.exp 1 * Real.log 2) := by
        rw [mul_div_assoc', div_le_div_iff₀ hl2 (by positivity)]
        have e : L / Real.exp 1 * (Real.exp 1 * Real.log 2) = L * Real.log 2 := by
          have := (Real.exp_pos 1).ne'
          field_simp
        have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ Real.exp 1 * Real.log 2)
        linarith
      linarith
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_range_succ_eq,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_ite_eq' (Finset.range L) 0,
    if_pos (Finset.mem_range.2 (by omega))] at this
  calc (L : ℝ) * (L + 1) / 2 * Real.log (Real.log L) -
        (L : ℝ) ^ 2 / (Real.exp 1 * Real.log 2) - Real.log (Real.log L)
      = (L : ℝ) * (L + 1) / 2 * Real.log (Real.log L) -
          L * (L / (Real.exp 1 * Real.log 2)) - Real.log (Real.log L) := by ring
    _ ≤ _ := this

/-- `∑_{k ≤ L} k log log k ≤ (L(L + 1)/2) log log L` for `L ≥ 3`. -/
theorem sum_mul_log_log_le {L : ℕ} (hL : 3 ≤ L) :
    ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (Real.log ((i : ℝ) + 1)) ≤
      (L : ℝ) * (L + 1) / 2 * Real.log (Real.log L) := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  rw [← sum_range_succ_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hiL := Finset.mem_range.1 hi
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [Nat.cast_zero, zero_add, Real.log_one, Real.log_zero]
    exact Real.log_nonneg hlogL
  · have hk : (2 : ℝ) ≤ (i : ℝ) + 1 := by
      have : (1 : ℝ) ≤ i := by exact_mod_cast h0
      linarith
    exact Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith)
      (by exact_mod_cast (show i + 1 ≤ L by omega)))

end CoefficientMass
