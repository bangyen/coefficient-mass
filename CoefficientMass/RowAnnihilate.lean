/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDefs

/-!
# The Annihilation Identity

This module proves the step of Lemma 4.5 of `coefficient-mass.tex` that uses
the root: a multiple of `(x - r)^L` is annihilated by `∑_j f_j q(j) r^j` for
every polynomial `q` of degree below `L`, the operator form
`ψ(D - θ) F (r) = 0` of the paper (`r = 2` there, any `r ≠ 0` for the rows at a general
root).  One factor `x - r` turns `q` into its forward difference,
which lowers the degree.

## Theorems

* `degree_forwardDiff_lt`.
* `sum_mul_X_sub_C`.
* `sum_coeff_mul_eval_eq_zero`.
-/

open Polynomial

namespace CoefficientMass

/-- The forward difference `q(x + 1) - q(x)` lowers the degree. -/
theorem degree_forwardDiff_lt {q : ℝ[X]} (hq : q ≠ 0) (hdeg : 0 < q.natDegree) :
    (q.comp (X + 1) - q).degree < q.degree := by
  have h1 : (X + 1 : ℝ[X]).natDegree = 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one, natDegree_X]; exact one_pos),
      natDegree_X]
  have hlc : (X + 1 : ℝ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, h1, coeff_add, coeff_X_one, coeff_one]
    norm_num
  have hcomp : (q.comp (X + 1)).natDegree = q.natDegree := by
    rw [natDegree_comp, h1, mul_one]
  have hne : q.comp (X + 1) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hcomp
    omega
  refine degree_sub_lt ?_ hne ?_ |>.trans_eq ?_
  · rw [degree_eq_natDegree hne, degree_eq_natDegree hq, hcomp]
  · rw [leadingCoeff_comp (by rw [h1]; norm_num), hlc, one_pow, mul_one]
  · rw [degree_eq_natDegree hne, degree_eq_natDegree hq, hcomp]

/-- One factor `x - r`: the sum against `q` becomes the sum against
`r (q(x + 1) - q(x))`. -/
theorem sum_mul_X_sub_C (r : ℝ) (H : ℝ[X]) (q : ℝ[X]) {N : ℕ} (hN : H.natDegree < N) :
    ∑ j ∈ Finset.range (N + 1), (H * (X - C r)).coeff j * q.eval (j : ℝ) * r ^ j =
      ∑ j ∈ Finset.range N,
        H.coeff j * (C r * (q.comp (X + 1) - q)).eval (j : ℝ) * r ^ j := by
  have hHN : H.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hN
  rw [Finset.sum_range_succ']
  simp only [coeff_mul_X_sub_C, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
    eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_C]
  have hsplit : ∀ j : ℕ,
      (H.coeff j - H.coeff (j + 1) * r) * q.eval ((j + 1 : ℕ) : ℝ) * r ^ (j + 1) =
        H.coeff j * q.eval ((j : ℝ) + 1) * r ^ (j + 1) -
          H.coeff (j + 1) * q.eval ((j + 1 : ℕ) : ℝ) * r ^ (j + 1 + 1) := by
    intro j
    push_cast
    ring
  simp only [hsplit, Finset.sum_sub_distrib]
  have htel : ∑ j ∈ Finset.range N, H.coeff (j + 1) * q.eval ((j + 1 : ℕ) : ℝ) * r ^ (j + 1 + 1) +
      H.coeff 0 * q.eval ((0 : ℕ) : ℝ) * r ^ 1 =
        ∑ j ∈ Finset.range N, H.coeff j * q.eval (j : ℝ) * r ^ (j + 1) := by
    rw [← Finset.sum_range_succ' (fun j => H.coeff j * q.eval (j : ℝ) * r ^ (j + 1)),
      Finset.sum_range_succ, hHN, zero_mul, zero_mul, add_zero]
  have hsum : ∑ j ∈ Finset.range N,
      H.coeff j * (r * (q.eval ((j : ℝ) + 1) - q.eval (j : ℝ))) * r ^ j =
        ∑ j ∈ Finset.range N, H.coeff j * q.eval ((j : ℝ) + 1) * r ^ (j + 1) -
          ∑ j ∈ Finset.range N, H.coeff j * q.eval (j : ℝ) * r ^ (j + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, ← htel]
  simp only [Nat.cast_zero, pow_one]
  ring

/-- The operator identity `ψ(D - θ) F (r) = 0`: a multiple of `(x - r)^L`
is annihilated by `∑_j f_j q(j) r^j` whenever `deg q < L`. -/
theorem sum_coeff_mul_eval_eq_zero {r : ℝ} (hr : r ≠ 0) (L : ℕ) :
    ∀ (G q : ℝ[X]) (N : ℕ), q.degree < L → (G * (X - C r) ^ L).natDegree < N →
      ∑ j ∈ Finset.range N, (G * (X - C r) ^ L).coeff j * q.eval (j : ℝ) * r ^ j = 0 := by
  induction L with
  | zero =>
    intro G q N hq _
    have : q = 0 := by
      by_contra h
      rw [Nat.cast_zero] at hq
      exact absurd hq (not_lt.2 (zero_le_degree_iff.2 h))
    rw [this]
    simp only [eval_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  | succ L ih =>
    intro G q N hq hN
    by_cases hG : G = 0
    · rw [hG, zero_mul]
      simp only [coeff_zero, zero_mul, Finset.sum_const_zero]
    set H := G * (X - C r) ^ L with hH
    have hF : G * (X - C r) ^ (L + 1) = H * (X - C r) := by rw [hH, pow_succ, mul_assoc]
    have hHne : H ≠ 0 := mul_ne_zero hG (pow_ne_zero _ (X_sub_C_ne_zero r))
    have hdegF : (H * (X - C r)).natDegree = H.natDegree + 1 := by
      rw [natDegree_mul hHne (X_sub_C_ne_zero r), natDegree_X_sub_C]
    rw [hF] at hN ⊢
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_mul_X_sub_C r H q (by omega)]
    by_cases hq0 : q = 0
    · rw [hq0]
      simp only [zero_comp, sub_zero, mul_zero, eval_zero, zero_mul, Finset.sum_const_zero]
    by_cases hqd : q.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hqd, C_comp, sub_self, mul_zero]
      simp only [eval_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    refine ih G _ M ?_ (show H.natDegree < M by omega)
    have hlt := degree_forwardDiff_lt hq0 (Nat.pos_of_ne_zero hqd)
    have hqL : q.degree ≤ L := by
      rw [degree_eq_natDegree hq0] at hq ⊢
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hq)
    rw [degree_C_mul hr]
    exact lt_of_lt_of_le hlt hqL

end CoefficientMass
