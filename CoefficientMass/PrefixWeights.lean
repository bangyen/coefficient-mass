/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Convolving Prefix Weights

This module prepares Lemma 6.3 of `coefficient-mass-rows.tex`.  Counting subsets by their
`i`-th smallest element gives `ω_{i+m}(s) = ∑_{u + t = s} ω_i(u) ω_m(t)` for the weights
`ω_i(s) = binom(s - 1, i - 1) r^{-s}`, and `ν_m(n) |p(u)| ≤ ∑_t ω_m(t) |p(u + t)|`, since
`t ↦ p(u + t)/p(u)` lies in `Q_n`.

## Theorems

* `sum_antidiag_choose_mul`.
* `prefixWeight_zero`.
* `prefixWeight_add`.
* `nuR_mul_le_shift`.
* `abs_eval_add_le`.
-/

open Polynomial

namespace CoefficientMass

/-- `∑_{a + b = N} binom(a, p) binom(b, q) = binom(N + 1, p + q + 1)`. -/
theorem sum_antidiag_choose_mul (q N : ℕ) : ∀ p : ℕ,
    ∑ ij ∈ Finset.antidiagonal N, ij.1.choose p * ij.2.choose q = (N + 1).choose (p + q + 1) := by
  induction N with
  | zero =>
    intro p
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    dsimp only
    by_cases hpq : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := hpq
      rfl
    · have h1 : Nat.choose 0 p * Nat.choose 0 q = 0 := by
        rcases Nat.eq_zero_or_pos p with hp | hp
        · rw [Nat.choose_eq_zero_of_lt (show 0 < q by omega), mul_zero]
        · rw [Nat.choose_eq_zero_of_lt hp, zero_mul]
      rw [h1, Nat.choose_eq_zero_of_lt (show 0 + 1 < p + q + 1 by omega)]
  | succ N ih =>
    intro p
    rw [Finset.Nat.sum_antidiagonal_succ]
    dsimp only
    rcases p with _ | p
    · have h0 := ih 0
      simp only [Nat.choose_zero_right, one_mul, zero_add] at h0 ⊢
      rw [h0]
      exact (Nat.choose_succ_succ (N + 1) q).symm
    · have hsplit : ∀ ij ∈ Finset.antidiagonal N, (ij.1 + 1).choose (p + 1) * ij.2.choose q =
          ij.1.choose p * ij.2.choose q + ij.1.choose (p + 1) * ij.2.choose q :=
        fun ij _ => by rw [Nat.choose_succ_succ, add_mul]
      rw [Nat.choose_eq_zero_of_lt (show 0 < p + 1 by omega), zero_mul, zero_add,
        Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ih p, ih (p + 1),
        show p + 1 + q + 1 = p + q + 1 + 1 by omega, Nat.choose_succ_succ (N + 1) (p + q + 1)]

theorem prefixWeight_zero (r : ℝ) (i : ℕ) : prefixWeight r i 0 = 0 := by
  unfold prefixWeight
  exact if_neg (by norm_num)

/-- `ω_{i+m}(s) = ∑_{u + t = s} ω_i(u) ω_m(t)`. -/
theorem prefixWeight_add (r : ℝ) {i m : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (s : ℕ) :
    prefixWeight r (i + m) s =
      ∑ x ∈ Finset.antidiagonal s, prefixWeight r i x.1 * prefixWeight r m x.2 := by
  rcases s with _ | _ | N
  · rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    dsimp only
    rw [prefixWeight_zero, prefixWeight_zero, zero_mul]
  · rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    dsimp only
    rw [prefixWeight_zero, prefixWeight_zero, zero_mul, mul_zero, add_zero]
    unfold prefixWeight
    rw [if_pos (show 1 ≤ 0 + 1 by omega),
      Nat.choose_eq_zero_of_lt (show 0 + 1 - 1 < i + m - 1 by omega), Nat.cast_zero, zero_mul]
  · rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    dsimp only
    rw [prefixWeight_zero, prefixWeight_zero, zero_mul, mul_zero, zero_add, zero_add]
    have hterm : ∀ x ∈ Finset.antidiagonal N,
        prefixWeight r i (x.1 + 1) * prefixWeight r m (x.2 + 1) =
          ((x.1.choose (i - 1) * x.2.choose (m - 1) : ℕ) : ℝ) * (1 / r) ^ (N + 1 + 1) :=
      fun x hx => by
        rw [Finset.mem_antidiagonal] at hx
        unfold prefixWeight
        rw [if_pos (show 1 ≤ x.1 + 1 by omega), if_pos (show 1 ≤ x.2 + 1 by omega),
          Nat.add_sub_cancel, Nat.add_sub_cancel, ← hx]
        push_cast
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum,
      sum_antidiag_choose_mul (m - 1) N (i - 1)]
    unfold prefixWeight
    rw [if_pos (show 1 ≤ N + 1 + 1 by omega), Nat.add_sub_cancel,
      show i - 1 + (m - 1) + 1 = i + m - 1 by omega]

/-- `ν_m(n) |p(u)| ≤ ∑_t ω_m(t) |p(u + t)|` for `deg p < n`. -/
theorem nuR_mul_le_shift {r : ℝ} (hr : 1 < r) (m : ℕ) {n : ℕ} {p : ℝ[X]} (hp : p.degree < n)
    (u : ℕ) : nuR r m n * |p.eval (u : ℝ)| ≤
      ∑' t : ℕ, prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)| := by
  by_cases hu : p.eval (u : ℝ) = 0
  · rw [hu, abs_zero, mul_zero]
    exact tsum_nonneg fun t => mul_nonneg (prefixWeight_le hr m t).1 (abs_nonneg _)
  have hpne : p ≠ 0 := fun h => hu (by rw [h, eval_zero])
  have hq : ∀ t : ℝ, (C (1 / p.eval (u : ℝ)) * p.comp (X + C (u : ℝ))).eval t =
      p.eval (t + u) / p.eval (u : ℝ) := fun t => by
    rw [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C]
    ring
  have hq0 : (C (1 / p.eval (u : ℝ)) * p.comp (X + C (u : ℝ))).eval 0 = 1 := by
    rw [hq, zero_add, div_self hu]
  have hqn : (C (1 / p.eval (u : ℝ)) * p.comp (X + C (u : ℝ))).degree < n := by
    have hpn : p.natDegree < n := by
      rw [degree_eq_natDegree hpne] at hp
      exact_mod_cast hp
    have : (C (1 / p.eval (u : ℝ)) * p.comp (X + C (u : ℝ))).natDegree ≤ p.natDegree :=
      (natDegree_C_mul_le _ _).trans (by rw [natDegree_comp, natDegree_X_add_C, mul_one])
    exact degree_le_natDegree.trans_lt (by exact_mod_cast this.trans_lt hpn)
  have hν := nuR_le_prefA hr m hqn hq0
  have hA : prefA r m (C (1 / p.eval (u : ℝ)) * p.comp (X + C (u : ℝ))) =
      (∑' t : ℕ, prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)|) / |p.eval (u : ℝ)| := by
    rw [prefA, ← tsum_div_const]
    refine tsum_congr fun t => ?_
    rw [hq, abs_div, Nat.cast_add, add_comm (t : ℝ)]
    ring
  rw [hA, le_div_iff₀ (abs_pos.2 hu)] at hν
  exact hν

/-- `|p(u + t)| ≤ (K (1 + u)^{n - 1}) (1 + t)^{n - 1}` for `deg p < n`. -/
theorem abs_eval_add_le {p : ℝ[X]} {n : ℕ} (hpn : p.natDegree < n) (u t : ℕ) :
    |p.eval ((u + t : ℕ) : ℝ)| ≤
      (∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j|) * (1 + (u : ℝ)) ^ (n - 1) *
        (1 + (t : ℝ)) ^ (n - 1) := by
  have hK : 0 ≤ ∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (abs_eval_le_pow hpn (Nat.cast_nonneg _)).trans ?_
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hK
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  push_cast
  nlinarith

end CoefficientMass
