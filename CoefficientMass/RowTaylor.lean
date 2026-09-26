/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDualLower
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Divisibility by `(x - r)^L` as Linear Conditions

This module prepares the upper bound of Proposition 2.1(b) of `coefficient-mass-rows.tex`.
A polynomial is divisible by `(x - r)^L` once its Hasse derivatives of order below `L`
vanish at `r`, by Taylor expansion at `r`.  For `F = x^D + ∑_{j < D} g_j x^j` these are the
`L` linear conditions `∑_j binom(j, i) g_j r^j + binom(D, i) r^D = 0`, `i < L`, and a
combination `∑_i c_i binom(s, i)` of the binomial polynomials is a polynomial of degree
below `L` in `s`.

## Definitions

* `rowPoly`.
* `binomPoly`.

## Theorems

* `dvd_of_hasseDeriv`.
* `rowPoly_monic`.
* `rowPoly_natDegree`.
* `rowPoly_coeff`.
* `choose_mul_pow_sub`.
* `hasseDeriv_rowPoly`.
* `binomPoly_eval`.
* `binomPoly_natDegree`.
-/

open Polynomial

namespace CoefficientMass

/-- `x^D + ∑_{j < D} g_j x^j`. -/
noncomputable def rowPoly (D : ℕ) (g : Fin D → ℝ) : ℝ[X] :=
  X ^ D + ∑ j : Fin D, C (g j) * X ^ (j : ℕ)

/-- `binom(s, i)` as a polynomial in `s`. -/
noncomputable def binomPoly (i : ℕ) : ℝ[X] :=
  C (1 / (i.factorial : ℝ)) * descPochhammer ℝ i

/-- Taylor expansion at `r`: vanishing Hasse derivatives give divisibility. -/
theorem dvd_of_hasseDeriv {r : ℝ} {L : ℕ} {F : ℝ[X]}
    (h : ∀ i < L, (hasseDeriv i F).eval r = 0) : (X - C r) ^ L ∣ F := by
  obtain ⟨G, hG⟩ : X ^ L ∣ taylor r F :=
    X_pow_dvd_iff.2 fun d hd => by rw [taylor_coeff]; exact h d hd
  refine ⟨G.comp (X - C r), ?_⟩
  have hF : F = (taylor r F).comp (X - C r) := by
    rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  rw [hF, hG, mul_comp, X_pow_comp]

theorem rowPoly_monic (D : ℕ) (g : Fin D → ℝ) : (rowPoly D g).Monic :=
  monic_X_pow_add (degree_sum_fin_lt g)

theorem rowPoly_natDegree (D : ℕ) (g : Fin D → ℝ) : (rowPoly D g).natDegree = D := by
  rw [rowPoly, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt g

theorem rowPoly_coeff (D : ℕ) (g : Fin D → ℝ) (j : Fin D) : (rowPoly D g).coeff j = g j := by
  have hsum : ∑ i : Fin D, (C (g i) * X ^ (i : ℕ)).coeff j = g j := by
    rw [Fintype.sum_eq_single j fun i hi => by
      rw [coeff_C_mul_X_pow, if_neg fun h => hi (Fin.ext h.symm)]]
    rw [coeff_C_mul_X_pow, if_pos rfl]
  rw [rowPoly, coeff_add, coeff_X_pow, if_neg j.is_lt.ne, zero_add, finset_sum_coeff, hsum]

theorem choose_mul_pow_sub (r : ℝ) (i j : ℕ) :
    r ^ i * ((j.choose i : ℝ) * r ^ (j - i)) = j.choose i * r ^ j := by
  rcases le_or_gt i j with h | h
  · rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' h]
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, mul_zero, zero_mul]

/-- `r^i (∂^{(i)} F)(r) = binom(D, i) r^D + ∑_j binom(j, i) g_j r^j`. -/
theorem hasseDeriv_rowPoly (r : ℝ) (D : ℕ) (g : Fin D → ℝ) (i : ℕ) :
    r ^ i * (hasseDeriv i (rowPoly D g)).eval r =
      D.choose i * r ^ D + ∑ j : Fin D, (j : ℕ).choose i * r ^ (j : ℕ) * g j := by
  rw [rowPoly, map_add, map_sum, eval_add, eval_finset_sum, mul_add, Finset.mul_sum,
    ← monomial_one_right_eq_X_pow, hasseDeriv_monomial, eval_monomial,
    ← choose_mul_pow_sub r i D]
  refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun j _ => ?_)
  rw [C_mul_X_pow_eq_monomial, hasseDeriv_monomial, eval_monomial,
    ← choose_mul_pow_sub r i j]
  ring

theorem binomPoly_eval (i n : ℕ) : (binomPoly i).eval (n : ℝ) = n.choose i := by
  rw [binomPoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ this, one_mul]

theorem binomPoly_natDegree (i : ℕ) : (binomPoly i).natDegree ≤ i :=
  (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree (R := ℝ) i).le

end CoefficientMass
