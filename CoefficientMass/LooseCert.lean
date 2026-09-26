/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FirstRow

/-!
# The Certificate on `{2, …, L}`

This module computes the tail of the certificate of Proposition 4.1 of
`coefficient-mass.tex`.  On the nodes `y_i = 1/r_i` with zero set `{2, …, L}`, the dual
identity with `P = ∏ (x - r_i)` reads `1 - S w_1 = 0`, so `w_1 = 1/S` with `S = ∑ r_i`.
The shifted sum `w_{d+1} / w_1` is the certificate on `{1, …, L - 1}`, whose tail is
`1/B` by Lemma 2.1, `B = ∏ (r_i - 1)`; so `Tail(w) = (1 + 1/B)/S`.

## Theorems

* `eval_rootProduct_inv`.
* `expSum_one_mul_sum`.
* `hasSum_shift_tail`.
-/

open Polynomial

namespace CoefficientMass

theorem eval_rootProduct_inv {L : ℕ} (r : Fin L → ℝ) (Q : ℝ[X]) (k : Fin L) :
    (rootProduct ℝ r * Q).eval ((r (Fin.rev k))⁻¹)⁻¹ = 0 := by
  rw [inv_inv, Polynomial.eval_mul, rootProduct, Polynomial.eval_prod,
    Finset.prod_eq_zero (Finset.mem_univ (Fin.rev k)), zero_mul]
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

/-- `w_1 S = 1` for the certificate on `{2, …, L}`. -/
theorem expSum_one_mul_sum {L : ℕ} (hL : 0 < L) (r : Fin L → ℝ) (hr : ∀ i, 1 < r i)
    (a : Fin L → ℝ) (ha : IsCertificate a (fun k => (r (Fin.rev k))⁻¹) (Finset.Ioo 1 (L + 1))) :
    expSum a (fun k => (r (Fin.rev k))⁻¹) 1 * ∑ i, r i = 1 := by
  set y : Fin L → ℝ := fun k => (r (Fin.rev k))⁻¹
  have hy : ∀ i, y i ≠ 0 := fun i => inv_ne_zero (by linarith [hr (Fin.rev i)])
  have hdual := sum_coeff_mul_expSum a y hy (rootProduct ℝ r) fun k => by
    have := eval_rootProduct_inv r 1 k
    rwa [mul_one] at this
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have hdeg := natDegree_rootProduct r
  rw [hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self, ha.1, mul_one,
    show M + 1 - M = 1 by omega] at hdual
  have hlead : (rootProduct ℝ r).coeff (M + 1) = 1 := by
    rw [← hdeg]
    exact (rootProduct_monic r).leadingCoeff
  have hnext : (rootProduct ℝ r).coeff M = -∑ i, r i := by
    have h := nextCoeff_of_natDegree_pos (p := rootProduct ℝ r) (by omega)
    rw [hdeg, Nat.add_sub_cancel] at h
    rw [← h, rootProduct]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    exact prod_X_sub_C_nextCoeff _
  have hzero : ∑ j ∈ Finset.range M, (rootProduct ℝ r).coeff j * expSum a y (M + 1 - j) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have := Finset.mem_range.1 hj
      rw [ha.2 _ (Finset.mem_Ioo.2 ⟨by omega, by omega⟩), mul_zero]
  rw [hzero, hlead, hnext, zero_add] at hdual
  linarith

/-- The tail of the shifted certificate: `∑_{d ≥ 1} |w_{d+1}| = |w_1| / B`. -/
theorem hasSum_shift_tail {L : ℕ} (hL : 0 < L) (r : Fin L → ℝ) (hmono : StrictMono r)
    (hr : ∀ i, 1 < r i) (a : Fin L → ℝ)
    (ha : IsCertificate a (fun k => (r (Fin.rev k))⁻¹) (Finset.Ioo 1 (L + 1)))
    (hw : expSum a (fun k => (r (Fin.rev k))⁻¹) 1 ≠ 0) :
    HasSum (fun d => |expSum a (fun k => (r (Fin.rev k))⁻¹) (d + 1 + 1)|)
      (|expSum a (fun k => (r (Fin.rev k))⁻¹) 1| * (∏ i, (r i - 1))⁻¹) := by
  set y : Fin L → ℝ := fun k => (r (Fin.rev k))⁻¹ with hy
  set w1 := expSum a y 1
  have hypos : ∀ k, 0 < y k := fun k => inv_pos.2 (by linarith [hr (Fin.rev k)])
  have hy1 : ∀ k, y k < 1 := fun k => inv_lt_one_of_one_lt₀ (hr _)
  have hymono : StrictMono y := fun k k' hkk' =>
    (inv_lt_inv₀ (by linarith [hr (Fin.rev k)]) (by linarith [hr (Fin.rev k')])).2
      (hmono (Fin.rev_lt_rev.2 hkk'))
  set a' : Fin L → ℝ := fun i => a i * y i / w1
  have hshift : ∀ d, expSum a' y d = expSum a y (d + 1) / w1 := fun d => by
    rw [expSum, expSum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  have ha' : IsCertificate a' y (Finset.Ioo 0 L) := by
    refine ⟨by rw [hshift, Nat.zero_add, div_self hw], fun z hz => ?_⟩
    have := Finset.mem_Ioo.1 hz
    rw [hshift, ha.2 _ (Finset.mem_Ioo.2 ⟨by omega, by omega⟩), zero_div]
  have hsum := consecutiveTail L a' y hymono hypos hy1 ha'
  have hprod : ∏ i, y i / (1 - y i) = (∏ i, (r i - 1))⁻¹ := by
    have h := nodeProduct_inv_rev r hr 0 hL
    have e1 : Finset.univ.filter (fun i : Fin L => i.val ≤ L - 1 - 0) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by have := i.isLt; omega
    have e2 : Finset.univ.filter (fun i : Fin L => 0 ≤ i.val) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => Nat.zero_le _
    rw [nodeProduct, e1, e2] at h
    exact h
  rw [hprod] at hsum
  have h := hsum.mul_left |w1|
  convert h using 1
  funext d
  rw [hshift, abs_div, mul_div_assoc', mul_div_cancel_left₀ _ (abs_ne_zero.2 hw)]

end CoefficientMass
