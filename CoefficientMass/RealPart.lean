/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Order

/-!
# Complex Multiples through the Real Part

This module proves Corollary 3.3 of `coefficient-mass.tex` from Theorem 3.2.
Normalize a complex multiple `F` of the real-rooted product `P` to leading
coefficient one; its coefficientwise real part is a monic real multiple of
`P` of the same degree, because `P` has real coefficients, and each of its
coefficient magnitudes is at most the complex one.

## Definitions

* `realPart`.

## Theorems

* `coeff_realPart`.
* `realPart_map_mul`.
* `rootProduct_complex`.
* `complexOrderStatistics_of_orderStatistics`.
-/

open Polynomial

namespace CoefficientMass

/-- The coefficientwise real part of a complex polynomial. -/
noncomputable def realPart (p : ℂ[X]) : ℝ[X] :=
  ∑ j ∈ p.support, monomial j (p.coeff j).re

theorem coeff_realPart (p : ℂ[X]) (n : ℕ) : (realPart p).coeff n = (p.coeff n).re := by
  rw [realPart, finset_sum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, Complex.zero_re]

/-- The real part of a real polynomial times a complex one is the real
polynomial times the real part. -/
theorem realPart_map_mul (A : ℝ[X]) (Q : ℂ[X]) :
    realPart (A.map (algebraMap ℝ ℂ) * Q) = A * realPart Q := by
  ext n
  rw [coeff_realPart, coeff_mul, coeff_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_realPart, Complex.coe_algebraMap, Complex.re_ofReal_mul]

/-- The complex root product is the real one with its coefficients mapped. -/
theorem rootProduct_complex {L : ℕ} (r : Fin L → ℝ) :
    rootProduct ℂ r = (rootProduct ℝ r).map (algebraMap ℝ ℂ) := by
  simp only [rootProduct, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- Corollary 3.3 from Theorem 3.2: the rows hold for complex multiples. -/
theorem complexOrderStatistics_of_orderStatistics (h : OrderStatistics) :
    ComplexOrderStatistics := by
  intro L r F hmono hr hF hdvd u
  have hc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hF
  obtain ⟨Q, hQ⟩ := hdvd
  set G := realPart (C F.leadingCoeff⁻¹ * F) with hGdef
  have hcoeff : ∀ n, G.coeff n = (F.leadingCoeff⁻¹ * F.coeff n).re := fun n => by
    rw [hGdef, coeff_realPart, coeff_C_mul]
  have htop : G.coeff F.natDegree = 1 := by
    rw [hcoeff, ← leadingCoeff, inv_mul_cancel₀ hc, Complex.one_re]
  have hdeg : G.natDegree = F.natDegree := by
    refine le_antisymm ((natDegree_le_iff_coeff_eq_zero).2 fun n hn => ?_)
      (le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero))
    rw [hcoeff, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn), mul_zero, Complex.zero_re]
  have hlead : G.leadingCoeff = 1 := by rw [leadingCoeff, hdeg, htop]
  have hG0 : G ≠ 0 := fun h0 => by rw [h0, leadingCoeff_zero] at hlead; exact zero_ne_one hlead
  have hGdvd : rootProduct ℝ r ∣ G := ⟨realPart (C F.leadingCoeff⁻¹ * Q), by
    rw [hGdef, ← realPart_map_mul, ← rootProduct_complex, hQ, mul_left_comm]⟩
  have hrow := h L r G hmono hr hG0 hGdvd u
  rw [hlead, norm_one, one_mul] at hrow
  refine hrow.trans (Finset.card_le_card fun j hj => ?_)
  rw [Finset.mem_filter] at hj ⊢
  rw [hdeg] at hj
  refine ⟨hj.1, ?_⟩
  have hle : ‖G.coeff j‖ ≤ ‖F.coeff j‖ / ‖F.leadingCoeff‖ := by
    rw [hcoeff, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_inv, div_eq_inv_mul]
  rw [mul_comm, ← le_div_iff₀ (norm_pos_iff.2 hc)]
  exact hj.2.trans hle

end CoefficientMass
