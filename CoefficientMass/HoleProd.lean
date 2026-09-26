/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleSum
import CoefficientMass.RowCert
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Products of the Hole Formula

This module collects the finite identities behind Lemma 4.7 of
`coefficient-mass.tex`: the partial fractions
`∏_{c ∈ C} c / (x - c) = ∑_{c ∈ C} π_c / (x - c)` from Lagrange
interpolation, the product `∏_{p ≤ N} (s - p) / p = C(s - 1, N)` for
`s > N`, and the product `∏_{p ≤ N, p ≠ c} |p - c| / p = c (c - 1)! (N - c)! / N!`
behind the values at the holes.

## Definitions

* `holeWeight`.
* `holeFactor`.

## Theorems

* `prod_div_eq_sum`.
* `prod_Icc_sub_div`.
* `prod_holeFactor_le`.
* `prod_holeFactor`.
-/

open Polynomial

namespace CoefficientMass

/-- `π_c = ∏_{c' ∈ C} c' / ∏_{c' ∈ C \ {c}} (c - c')`. -/
noncomputable def holeWeight (C : Finset ℕ) (c : ℕ) : ℝ :=
  (∏ c' ∈ C, (c' : ℝ)) / ∏ c' ∈ C.erase c, ((c : ℝ) - c')

/-- The factor `|p - c| / p` of `|r_Y(c)|`, set to `1` at `p = c`. -/
noncomputable def holeFactor (c p : ℕ) : ℝ :=
  if p = c then 1 else |(p : ℝ) - c| / p

/-- Partial fractions: `∏_{c ∈ C} c / (x - c) = ∑_{c ∈ C} π_c / (x - c)`. -/
theorem prod_div_eq_sum {C : Finset ℕ} (hC : C.Nonempty) {x : ℝ} (hx : ∀ c ∈ C, x ≠ c) :
    ∏ c ∈ C, ((c : ℝ) / (x - c)) = ∑ c ∈ C, holeWeight C c / (x - c) := by
  have hinj : Set.InjOn (Nat.cast : ℕ → ℝ) C := fun a _ b _ h => Nat.cast_injective h
  have h1 := congrArg (Polynomial.eval x) (Lagrange.sum_basis hinj hC)
  rw [eval_finset_sum, eval_one, Finset.sum_congr rfl fun c hc =>
    Lagrange.eval_basis_not_at_node hc (hx c hc), Lagrange.eval_nodal, ← Finset.mul_sum] at h1
  have hS := eq_inv_of_mul_eq_one_right h1
  have e : ∀ c ∈ C, holeWeight C c / (x - c) = (∏ c' ∈ C, (c' : ℝ)) *
      (Lagrange.nodalWeight C (Nat.cast : ℕ → ℝ) c * (x - c)⁻¹) := fun c _ => by
    rw [holeWeight, Lagrange.nodalWeight, Finset.prod_inv_distrib]
    ring
  rw [Finset.prod_div_distrib, Finset.sum_congr rfl e, ← Finset.mul_sum, hS, div_eq_mul_inv]

/-- `∏_{p ≤ N} (s - p) / p = C(s - 1, N)` at `s = t + N + 1`. -/
theorem prod_Icc_sub_div (N : ℕ) : ∀ t : ℕ,
    ∏ p ∈ Finset.Icc 1 N, ((((t + N + 1 : ℕ) : ℝ) - p) / p) = ((t + N).choose N : ℝ) := by
  induction N with
  | zero =>
    intro t
    rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.prod_empty, Nat.choose_zero_right,
      Nat.cast_one]
  | succ N ih =>
    intro t
    have h := Nat.choose_succ_right_eq (t + (N + 1)) N
    rw [show t + (N + 1) - N = t + 1 by omega, show t + (N + 1) = t + 1 + N by ring] at h
    have hc : ((t + 1 + N).choose (N + 1) : ℝ) * (N + 1) =
        ((t + 1 + N).choose N : ℝ) * (t + 1) := by
      exact_mod_cast h
    rw [show t + (N + 1) = t + 1 + N by ring, Finset.prod_Icc_succ_top (by omega), ih (t + 1),
      mul_div_assoc', div_eq_iff (by positivity)]
    push_cast
    linear_combination -hc

/-- Below the hole: `∏_{p ≤ n} |p - c| / p = C(c - 1, n)` for `n < c`. -/
theorem prod_holeFactor_le (j : ℕ) : ∀ n, n ≤ j →
    ∏ p ∈ Finset.Icc 1 n, holeFactor (j + 1) p = (j.choose n : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.prod_empty, Nat.choose_zero_right,
      Nat.cast_one]
  | succ n ih =>
    intro hn
    have h := Nat.choose_succ_right_eq j n
    have hc : (j.choose (n + 1) : ℝ) * (n + 1) = (j.choose n : ℝ) * ((j : ℝ) - n) := by
      rw [← Nat.cast_sub (by omega)]
      exact_mod_cast h
    have hab : |((n + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)| = (j : ℝ) - n := by
      rw [abs_of_nonpos (by push_cast; linarith [(by exact_mod_cast hn : (n : ℝ) + 1 ≤ j)])]
      push_cast
      ring
    rw [Finset.prod_Icc_succ_top (by omega), ih (by omega), holeFactor, if_neg (by omega), hab,
      mul_div_assoc', div_eq_iff (by positivity)]
    push_cast
    linear_combination -hc

/-- Through the hole: `∏_{p ≤ N} |p - c| / p = c (c - 1)! (N - c)! / N!` for `c ≤ N`. -/
theorem prod_holeFactor (j : ℕ) : ∀ k, ∏ p ∈ Finset.Icc 1 (j + 1 + k), holeFactor (j + 1) p =
    ((j + 1) * j.factorial * k.factorial : ℝ) / (j + 1 + k).factorial := by
  intro k
  induction k with
  | zero =>
    rw [Nat.add_zero, Finset.prod_Icc_succ_top (by omega), prod_holeFactor_le j j le_rfl,
      holeFactor, if_pos rfl, Nat.choose_self, Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    rw [eq_div_iff (by positivity)]
    ring
  | succ k ih =>
    have hab : |((j + 1 + k + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)| = (k : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
      ring
    rw [← add_assoc, Finset.prod_Icc_succ_top (by omega), ih, holeFactor, if_neg (by omega), hab,
      Nat.factorial_succ (j + 1 + k), Nat.factorial_succ k]
    push_cast
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring

end CoefficientMass
