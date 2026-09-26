/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LooseCert

/-!
# The First Row from the Certificate on `{2, …, L}`

This module proves the distinct-root case of Proposition 4.1 of `coefficient-mass.tex`.
With `Tail(w) = (1 + 1/B)/S`, the dual identity of Lemma 3.1 gives a nonleading
coefficient of `F` with `|f_j| ≥ |f_D| / Tail(w) = |f_D| S B / (B + 1)`.

## Theorems

* `looseCertificate`.
* `loose_count_distinct`.
-/

open Polynomial

namespace CoefficientMass

/-- Proposition 4.1 for distinct roots `1 < r_1 < ⋯ < r_L` and `|f_D| = 1`: some `j < D`
has `|f_j| ≥ S B / (B + 1)`. -/
theorem looseCertificate {L : ℕ} (hL : 0 < L) (r : Fin L → ℝ) (F : ℝ[X])
    (hmono : StrictMono r) (hr : ∀ i, 1 < r i) (hdvd : rootProduct ℝ r ∣ F)
    (hlead : ‖F.leadingCoeff‖ = 1) :
    ∃ j < F.natDegree,
      (∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1) ≤ ‖F.coeff j‖ := by
  classical
  set D := F.natDegree with hD
  set B := ∏ i, (r i - 1) with hB
  set S := ∑ i, r i with hS
  set y : Fin L → ℝ := fun k => (r (Fin.rev k))⁻¹ with hy
  have hypos : ∀ k, 0 < y k := fun k => inv_pos.2 (by linarith [hr (Fin.rev k)])
  have hymono : StrictMono y := fun k k' hkk' =>
    (inv_lt_inv₀ (by linarith [hr (Fin.rev k)]) (by linarith [hr (Fin.rev k')])).2
      (hmono (Fin.rev_lt_rev.2 hkk'))
  have hBpos : 0 < B := Finset.prod_pos fun i _ => by linarith [hr i]
  have hSpos : 0 < S :=
    Finset.sum_pos (fun i _ => by linarith [hr i]) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  have h0 : 0 ∉ Finset.Ioo 1 (L + 1) := fun h => by
    have := (Finset.mem_Ioo.1 h).1
    omega
  obtain ⟨a, ha⟩ := exists_certificate zeroBound y hymono.injective hypos
    (Finset.Ioo 1 (L + 1)) h0 (by rw [Nat.card_Ioo]; omega)
  have hw := expSum_one_mul_sum hL r hr a ha
  rw [← hy] at hw
  have hw0 : expSum a y 1 ≠ 0 := fun h => by
    rw [h, zero_mul] at hw
    exact zero_ne_one hw
  have hw1 : |expSum a y 1| = S⁻¹ := by
    rw [eq_inv_of_mul_eq_one_left hw, abs_inv, abs_of_pos hSpos]
  have htail := hasSum_shift_tail hL r hmono hr a ha hw0
  rw [← hy] at htail
  have hsum : HasSum (fun d => |expSum a y (d + 1)|)
      (|expSum a y 1| + |expSum a y 1| * B⁻¹) := by
    refine (hasSum_nat_add_iff' 1).1 ?_
    simp only [Finset.sum_range_one, Nat.zero_add, add_sub_cancel_left]
    exact htail
  -- the dual identity, with the leading term split off
  have hev : ∀ i, F.eval (y i)⁻¹ = 0 := fun i => by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ]
    exact eval_rootProduct_inv r Q i
  have hdual := sum_coeff_mul_expSum a y (fun i => (hypos i).ne') F hev
  rw [Finset.sum_range_succ, ← hD, Nat.sub_self, ha.1, mul_one] at hdual
  have hlead' : |F.coeff D| = 1 := by rw [← Real.norm_eq_abs]; exact hlead
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, Finset.range_zero, Finset.sum_empty, zero_add] at hdual
      rw [h, hdual, abs_zero] at hlead'
      exact absurd hlead' zero_ne_one
    · exact h
  obtain ⟨j, hjD, hjmax⟩ := (Finset.range D).exists_max_image (fun j => |F.coeff j|)
    ⟨0, Finset.mem_range.2 hDpos⟩
  refine ⟨j, Finset.mem_range.1 hjD, ?_⟩
  have hweight : ∑ k ∈ Finset.range D, |expSum a y (D - k)| ≤
      |expSum a y 1| + |expSum a y 1| * B⁻¹ := by
    rw [← hsum.tsum_eq, ← Finset.sum_range_reflect]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
      (hsum.summable.sum_le_tsum (Finset.range D) fun _ _ => abs_nonneg _)
    have := Finset.mem_range.1 hk
    change |expSum a y (D - (D - 1 - k))| = |expSum a y (k + 1)|
    rw [show D - (D - 1 - k) = k + 1 by omega]
  have h1 : 1 ≤ ∑ k ∈ Finset.range D, |F.coeff k| * |expSum a y (D - k)| := by
    rw [← hlead', eq_neg_of_add_eq_zero_right hdual, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => abs_mul _ _
  have hbound : 1 ≤ |F.coeff j| * (|expSum a y 1| + |expSum a y 1| * B⁻¹) := by
    refine h1.trans ((Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hjmax k hk) (abs_nonneg _)).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hweight (abs_nonneg _)
  rw [hw1] at hbound
  have hSB : 0 < S * B := mul_pos hSpos hBpos
  have hS0 : S ≠ 0 := hSpos.ne'
  have hB0 : B ≠ 0 := hBpos.ne'
  have e : |F.coeff j| * (S⁻¹ + S⁻¹ * B⁻¹) * (S * B) = |F.coeff j| * (B + 1) := by
    field_simp
  have k := mul_le_mul_of_nonneg_right hbound hSB.le
  rw [e, one_mul] at k
  rw [Real.norm_eq_abs, div_le_iff₀ (by linarith)]
  exact k

/-- The distinct case for any leading coefficient. -/
theorem loose_count_distinct {L : ℕ} (hL : 0 < L) (r : Fin L → ℝ) (G : ℝ[X])
    (hmono : StrictMono r) (hr : ∀ i, 1 < r i) (hG : G ≠ 0) (hdvd : rootProduct ℝ r ∣ G) :
    1 ≤ largeCount G (‖G.leadingCoeff‖ *
      ((∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1))) := by
  classical
  have hc0 : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hG
  have hn : 0 < ‖G.leadingCoeff‖ := norm_pos_iff.2 hc0
  obtain ⟨j, hjD, hj⟩ := looseCertificate hL r (C G.leadingCoeff⁻¹ * G) hmono hr
    (dvd_mul_of_dvd_right hdvd _) (by
      rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hc0, norm_one])
  rw [natDegree_C_mul (inv_ne_zero hc0)] at hjD
  rw [coeff_C_mul, norm_mul, norm_inv] at hj
  refine Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hjD, ?_⟩⟩
  calc ‖G.leadingCoeff‖ * ((∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1))
      ≤ ‖G.leadingCoeff‖ * (‖G.leadingCoeff‖⁻¹ * ‖G.coeff j‖) :=
        mul_le_mul_of_nonneg_left hj hn.le
    _ = ‖G.coeff j‖ := mul_inv_cancel_left₀ hn.ne' _

end CoefficientMass
