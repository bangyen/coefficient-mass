/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleBeta
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Tail Sums of the Hole Formula

This module evaluates the series behind Lemma 4.7 of `coefficient-mass.tex`,
`L(N, c) = ∑_{s > N} C(s - 1, N) 2^{-s} / (s - c)` for `1 ≤ c ≤ N`.  The
identity `(N + 1) C(s - 1, N + 1) = (s - 1 - N) C(s - 1, N)` and
`∑_{s > N} C(s - 1, N) 2^{-s} = 1` give
`(N + 1) L(N + 1, c) + (N + 1 - c) L(N, c) = 1`, the recursion of
`2^{-c} ∫_0^1 v^{N - c} (1 + v)^{c - 1} dv`, and the two agree at `N = c`.
So `L(N, c) = 2^{-c} ∫_0^1 v^{N - c} (1 + v)^{c - 1} dv` without exchanging a
sum and an integral.

## Definitions

* `holeL`.

## Theorems

* `summable_binomTerm`.
* `tsum_binomTerm`.
* `summable_holeL`.
* `holeL_base`.
* `holeL_rec`.
* `holeL_eq`.
-/

namespace CoefficientMass

/-- `L(N, c) = ∑_{s > N} C(s - 1, N) 2^{-s} / (s - c)`, indexed by `s = t + N + 1`. -/
noncomputable def holeL (N c : ℕ) : ℝ :=
  ∑' t : ℕ, ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) / (((t + N + 1 : ℕ) : ℝ) - c)

theorem summable_binomTerm (N : ℕ) :
    Summable fun t : ℕ => ((t + N).choose N : ℝ) * (1 / 2 : ℝ) ^ (t + N + 1) := by
  refine ((summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) N
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left ((1 / 2 : ℝ) ^ (N + 1))).congr fun t => ?_
  ring

/-- `∑_{s > N} C(s - 1, N) 2^{-s} = 1`. -/
theorem tsum_binomTerm (N : ℕ) :
    ∑' t : ℕ, ((t + N).choose N : ℝ) * (1 / 2 : ℝ) ^ (t + N + 1) = 1 := by
  have h := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) N
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have e : ∀ t : ℕ, ((t + N).choose N : ℝ) * (1 / 2 : ℝ) ^ (t + N + 1) =
      (1 / 2) ^ (N + 1) * (((t + N).choose N : ℝ) * (1 / 2) ^ t) := fun t => by
    ring
  rw [tsum_congr e, tsum_mul_left, h, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← mul_div_assoc,
    mul_one, div_self (by positivity)]

theorem summable_holeL {N c : ℕ} (hc : c ≤ N) :
    Summable fun t : ℕ =>
      ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) / (((t + N + 1 : ℕ) : ℝ) - c) := by
  refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_) (summable_binomTerm N)
  · have : (c : ℝ) < ((t + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : c < t + N + 1)
    exact div_nonneg (by positivity) (by linarith)
  · have : (1 : ℝ) ≤ ((t + N + 1 : ℕ) : ℝ) - c := by
      have : (c : ℝ) + 1 ≤ ((t + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : c + 1 ≤ t + N + 1)
      linarith
    exact div_le_self (by positivity) this

/-- `L(c, c) = (1 - 2^{-c}) / c`. -/
theorem holeL_base (j : ℕ) :
    holeL (j + 1) (j + 1) = (1 / 2) ^ (j + 1) * ((2 ^ (j + 1) - 1) / (j + 1)) := by
  have hs := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) j
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have ht := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) j
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  rw [hs.tsum_eq_zero_add] at ht
  simp only [zero_add, Nat.choose_self, Nat.cast_one, pow_zero, mul_one] at ht
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have e : ∀ t : ℕ, ((t + (j + 1)).choose (j + 1) : ℝ) * (1 / 2) ^ (t + (j + 1) + 1) /
      (((t + (j + 1) + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) =
      (1 / 2) ^ (j + 1) / (j + 1) * (((t + 1 + j).choose j : ℝ) * (1 / 2) ^ (t + 1)) := by
    intro t
    have hc : ((t + (j + 1)).choose (j + 1) : ℝ) * (j + 1) =
        ((t + 1 + j).choose j : ℝ) * (t + 1) := by
      have h := Nat.choose_succ_right_eq (t + (j + 1)) j
      rw [show t + (j + 1) - j = t + 1 by omega] at h
      rw [show t + 1 + j = t + (j + 1) by omega]
      exact_mod_cast h
    have hden : ((t + (j + 1) + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) = t + 1 := by
      push_cast
      ring
    rw [hden, div_eq_iff (by positivity), show (1 / 2 : ℝ) ^ (j + 1) / (j + 1) *
      (((t + 1 + j).choose j : ℝ) * (1 / 2) ^ (t + 1)) * (t + 1) = (1 / 2) ^ (j + 1) *
      (1 / 2) ^ (t + 1) * (((t + 1 + j).choose j : ℝ) * (t + 1)) / (j + 1) by ring, ← hc,
      mul_div_assoc, mul_div_cancel_right₀ _ hj]
    ring
  rw [holeL, tsum_congr e, tsum_mul_left]
  have h2 : (1 : ℝ) / (1 - 1 / 2) ^ (j + 1) = 2 ^ (j + 1) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow, one_div_one_div]
  have hS : ∑' t : ℕ, ((t + 1 + j).choose j : ℝ) * (1 / 2) ^ (t + 1) = 2 ^ (j + 1) - 1 := by
    rw [h2] at ht
    linarith
  rw [hS]
  ring

/-- `(N + 1) L(N + 1, c) + (N + 1 - c) L(N, c) = 1` for `c ≤ N`. -/
theorem holeL_rec {N c : ℕ} (hc : c ≤ N) :
    ((N : ℝ) + 1) * holeL (N + 1) c + ((N : ℝ) + 1 - c) * holeL N c = 1 := by
  set A : ℕ → ℝ := fun t => ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) with hA
  set T : ℕ → ℝ := fun t =>
    ((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) / (((t + N + 1 : ℕ) : ℝ) - c) with hT
  have hAs : Summable A := summable_binomTerm N
  have hTs : Summable T := summable_holeL hc
  have hNc : (N : ℝ) + 1 - c ≠ 0 := by
    have : (c : ℝ) ≤ N := by exact_mod_cast hc
    linarith
  have e : ∀ t : ℕ, ((N : ℝ) + 1) * (((t + (N + 1)).choose (N + 1) : ℝ) *
      (1 / 2) ^ (t + (N + 1) + 1) / (((t + (N + 1) + 1 : ℕ) : ℝ) - c)) =
      A (t + 1) - ((N : ℝ) + 1 - c) * T (t + 1) := by
    intro t
    have hch : ((t + (N + 1)).choose (N + 1) : ℝ) * (N + 1) =
        ((t + 1 + N).choose N : ℝ) * (t + 1) := by
      have h := Nat.choose_succ_right_eq (t + (N + 1)) N
      rw [show t + (N + 1) - N = t + 1 by omega] at h
      rw [show t + 1 + N = t + (N + 1) by omega]
      exact_mod_cast h
    have hpos : (0 : ℝ) < ((t + (N + 1) + 1 : ℕ) : ℝ) - c := by
      have : (c : ℝ) < ((t + (N + 1) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : c < t + (N + 1) + 1)
      linarith
    simp only [hA, hT]
    rw [show t + 1 + N + 1 = t + (N + 1) + 1 by omega]
    set D : ℝ := ((t + (N + 1) + 1 : ℕ) : ℝ) - c with hD
    set C1 : ℝ := ((t + (N + 1)).choose (N + 1) : ℝ)
    set C2 : ℝ := ((t + 1 + N).choose N : ℝ)
    set R : ℝ := (1 / 2 : ℝ) ^ (t + (N + 1) + 1)
    have hDv : D = t + N + 2 - c := by
      rw [hD]
      push_cast
      ring
    rw [show ((N : ℝ) + 1) * (C1 * R / D) = C2 * (t + 1) * R / D by rw [← hch]; ring,
      eq_sub_iff_add_eq, ← mul_div_assoc, div_add_div_same, div_eq_iff hpos.ne', hDv]
    ring
  have h1 : ((N : ℝ) + 1) * holeL (N + 1) c =
      ∑' t, (A (t + 1) - ((N : ℝ) + 1 - c) * T (t + 1)) := by
    rw [holeL, ← tsum_mul_left, tsum_congr e]
  have hA0 : A 0 = (1 / 2) ^ (N + 1) := by
    simp only [hA, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hT0 : T 0 = (1 / 2) ^ (N + 1) / ((N : ℝ) + 1 - c) := by
    simp only [hT, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    push_cast
  have hsumA := hAs.tsum_eq_zero_add
  have hsumT := hTs.tsum_eq_zero_add
  have hAt : ∑' t, A t = 1 := tsum_binomTerm N
  rw [h1, Summable.tsum_sub ((summable_nat_add_iff 1).2 hAs)
    (((summable_nat_add_iff 1).2 hTs).mul_left _), tsum_mul_left]
  rw [hA0] at hsumA
  rw [hT0] at hsumT
  have hL : holeL N c = ∑' t, T t := rfl
  have hk : ((N : ℝ) + 1 - c) * ((1 / 2) ^ (N + 1) / ((N : ℝ) + 1 - c)) =
      (1 / 2) ^ (N + 1) := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hNc
  rw [hL, hsumT, mul_add, hk]
  linarith

/-- Lemma 4.7, tail part: `L(N, c) = 2^{-c} ∫_0^1 v^{N - c} (1 + v)^{c - 1} dv`. -/
theorem holeL_eq (j k : ℕ) : holeL (k + j + 1) (j + 1) = (1 / 2) ^ (j + 1) * plusI k j := by
  induction k with
  | zero =>
    rw [Nat.zero_add, holeL_base, plusI_zero_left]
  | succ k ih =>
    have h1 := holeL_rec (N := k + j + 1) (c := j + 1) (by omega)
    have h2 := plusI_rec j k
    have hr : (1 / 2 : ℝ) ^ (j + 1) * 2 ^ (j + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [ih, show k + j + 1 + 1 = k + 1 + j + 1 by ring] at h1
    push_cast at h1
    have h3 : ((k : ℝ) + j + 2) * (holeL (k + 1 + j + 1) (j + 1) -
        (1 / 2) ^ (j + 1) * plusI (k + 1) j) = 0 := by
      linear_combination h1 - (1 / 2 : ℝ) ^ (j + 1) * h2 - hr
    have h4 : ((k : ℝ) + j + 2) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h3).resolve_left h4
    linarith

end CoefficientMass
