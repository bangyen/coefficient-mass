/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FirstRow

/-! # The Complex First Row Above One

This module completes Corollary 3.3 of `coefficient-mass.tex` by transferring
the extra first-row clause of Theorem 3.2 from real to complex multiples.
-/

open Polynomial

namespace CoefficientMass

/-- Corollary 3.3, the extra first-row clause for complex multiples. -/
def ComplexFirstRowOrderStatistics : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℂ[X]), 0 < L → Monotone r → (∀ i, 1 < r i) → F ≠ 0 →
    rootProduct ℂ r ∣ F → 1 ≤ largeCount F (‖F.leadingCoeff‖ * ∏ i, (r i - 1))

/-- Corollary 3.3, the first row above one, from the real first-row theorem. -/
theorem complexFirstRowOrderStatistics : ComplexFirstRowOrderStatistics := by
  intro L r F hL hmono hr hF hdvd
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
  have hrow := firstRowOrderStatistics L r G hL hmono hr hG0 hGdvd
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
