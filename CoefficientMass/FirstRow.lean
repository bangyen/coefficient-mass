/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Chain
import CoefficientMass.Consecutive

/-!
# The First Row Above One

This module proves the clauses of Lemma 3.1 and Theorem 3.2 of
`coefficient-mass.tex` that relax `r_1 ≥ 2` to `r_1 > 1` for the first row.
With no excluded positions the zero set is `{1, …, L - 1}`, and Lemma 2.1
evaluates its tail as `∏ y_i / (1 - y_i)` for all nodes in `(0, 1)`, so the
bound `y_i ≤ 1/2` of Theorem 2.2 is not needed.  Repeated roots are moved
apart as in the proof of Theorem 3.2.

## Definitions

* `FirstRowCertificate`.
* `FirstRowOrderStatistics`.

## Theorems

* `firstRowCertificate`.
* `firstRow_count_distinct`.
* `firstRowOrderStatistics`.
-/

open Polynomial Topology

namespace CoefficientMass

/-- Lemma 3.1 at `u = 0` with `r_1 > 1`: for distinct roots `1 < r_1 < ⋯ < r_L`
and a real multiple `F` with `|f_D| = 1`, some `j < D` has
`|f_j| ≥ ∏ (r_i - 1)`. -/
def FirstRowCertificate : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), 0 < L → StrictMono r → (∀ i, 1 < r i) →
    rootProduct ℝ r ∣ F → ‖F.leadingCoeff‖ = 1 →
      ∃ j < F.natDegree, ∏ i, (r i - 1) ≤ ‖F.coeff j‖

/-- Theorem 3.2 at `u = 0` with `r_1 > 1`: for real roots `1 < r_1 ≤ ⋯ ≤ r_L`,
repetitions allowed, and a nonzero real multiple `F`,
`b_1(F) ≥ |f_D| ∏ (r_i - 1)`. -/
def FirstRowOrderStatistics : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), 0 < L → Monotone r → (∀ i, 1 < r i) → F ≠ 0 →
    rootProduct ℝ r ∣ F → 1 ≤ largeCount F (‖F.leadingCoeff‖ * ∏ i, (r i - 1))

/-- Lemma 3.1 at `u = 0` from Lemma 2.1. -/
theorem firstRowCertificate : FirstRowCertificate := by
  classical
  intro L r F hL hmono hr hdvd hlead
  set D := F.natDegree with hD
  set T := ∏ i, (r i - 1) with hT
  set y : Fin L → ℝ := fun k => (r (Fin.rev k))⁻¹ with hy
  have hypos : ∀ k, 0 < y k := fun k => inv_pos.2 (by linarith [hr (Fin.rev k)])
  have hy1 : ∀ k, y k < 1 := fun k => inv_lt_one_of_one_lt₀ (hr _)
  have hymono : StrictMono y := fun k k' hkk' =>
    (inv_lt_inv₀ (by linarith [hr (Fin.rev k)]) (by linarith [hr (Fin.rev k')])).2
      (hmono (Fin.rev_lt_rev.2 hkk'))
  have hTpos : 0 < T := Finset.prod_pos fun i _ => by linarith [hr i]
  have h0 : 0 ∉ Finset.Ioo 0 L := fun h => lt_irrefl 0 (Finset.mem_Ioo.1 h).1
  obtain ⟨a, ha⟩ := exists_certificate zeroBound y hymono.injective hypos (Finset.Ioo 0 L) h0
    (by rw [Nat.card_Ioo]; omega)
  have hsum := consecutiveTail L a y hymono hypos hy1 ha
  have hprod : ∏ i, y i / (1 - y i) = T⁻¹ := by
    have h := nodeProduct_inv_rev r hr 0 hL
    have e1 : Finset.univ.filter (fun i : Fin L => i.val ≤ L - 1 - 0) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by have := i.isLt; omega
    have e2 : Finset.univ.filter (fun i : Fin L => 0 ≤ i.val) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => Nat.zero_le _
    rw [nodeProduct, e1, e2] at h
    exact h
  rw [hprod] at hsum
  -- the dual identity, with the leading term split off
  have hev : ∀ i, F.eval (y i)⁻¹ = 0 := fun i => by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hy, inv_inv, hQ, Polynomial.eval_mul, rootProduct, Polynomial.eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ (Fin.rev i)), zero_mul]
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
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
  have hweight : ∑ k ∈ Finset.range D, |expSum a y (D - k)| ≤ T⁻¹ := by
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
  have hbound : 1 ≤ |F.coeff j| * T⁻¹ := by
    refine h1.trans ((Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hjmax k hk) (abs_nonneg _)).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hweight (abs_nonneg _)
  rw [← div_eq_mul_inv, one_le_div₀ hTpos] at hbound
  rw [Real.norm_eq_abs]
  exact hbound

/-- The distinct case for any leading coefficient. -/
theorem firstRow_count_distinct {L : ℕ} (hL : 0 < L) (r : Fin L → ℝ) (G : ℝ[X])
    (hmono : StrictMono r) (hr : ∀ i, 1 < r i) (hG : G ≠ 0) (hdvd : rootProduct ℝ r ∣ G) :
    1 ≤ largeCount G (‖G.leadingCoeff‖ * ∏ i, (r i - 1)) := by
  classical
  have hc0 : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hG
  have hn : 0 < ‖G.leadingCoeff‖ := norm_pos_iff.2 hc0
  obtain ⟨j, hjD, hj⟩ := firstRowCertificate L r (C G.leadingCoeff⁻¹ * G) hL hmono hr
    (dvd_mul_of_dvd_right hdvd _) (by
      rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hc0, norm_one])
  rw [natDegree_C_mul (inv_ne_zero hc0)] at hjD
  rw [coeff_C_mul, norm_mul, norm_inv] at hj
  refine Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hjD, ?_⟩⟩
  calc ‖G.leadingCoeff‖ * ∏ i, (r i - 1)
      ≤ ‖G.leadingCoeff‖ * (‖G.leadingCoeff‖⁻¹ * ‖G.coeff j‖) :=
        mul_le_mul_of_nonneg_left hj hn.le
    _ = ‖G.coeff j‖ := mul_inv_cancel_left₀ hn.ne' _

/-- Theorem 3.2 at `u = 0` with `r_1 > 1`. -/
theorem firstRowOrderStatistics : FirstRowOrderStatistics := by
  classical
  intro L r F hL hmono hr hF hdvd
  obtain ⟨Q, hQ⟩ := hdvd
  have hQ0 : Q ≠ 0 := fun h => hF (by rw [hQ, h, mul_zero])
  set Fε : ℝ → ℝ[X] := fun ε => rootProduct ℝ (fun i => r i + (i.val : ℝ) * ε) * Q with hFε
  set Tε : ℝ → ℝ := fun ε => ‖F.leadingCoeff‖ * ∏ i, (r i + (i.val : ℝ) * ε - 1) with hTε
  have hF0 : Fε 0 = F := by
    simp only [hFε, mul_zero, add_zero]
    exact hQ.symm
  have hT0 : Tε 0 = ‖F.leadingCoeff‖ * ∏ i, (r i - 1) := by
    simp only [hTε, mul_zero, add_zero]
  have hdeg : ∀ ε, (Fε ε).natDegree = F.natDegree := fun ε => by
    rw [hQ, hFε, natDegree_mul (rootProduct_monic _).ne_zero hQ0,
      natDegree_mul (rootProduct_monic _).ne_zero hQ0, natDegree_rootProduct,
      natDegree_rootProduct]
  have hlc : ∀ ε, (Fε ε).leadingCoeff = F.leadingCoeff := fun ε => by
    rw [hQ, hFε, leadingCoeff_mul, leadingCoeff_mul, (rootProduct_monic _).leadingCoeff,
      (rootProduct_monic _).leadingCoeff]
  -- the positions that are small at `ε = 0` stay small for small `ε`
  set S := (Finset.range F.natDegree).filter fun j => ‖F.coeff j‖ < Tε 0 with hS
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j ∈ S, ‖(Fε ε).coeff j‖ < Tε ε := by
    refine (Filter.eventually_all_finset S).2 fun j hj => ?_
    refine ContinuousAt.eventually_lt ?_ ?_ ?_
    · exact (continuous_norm.comp (continuous_coeff_rootProduct_mul r Q j)).continuousAt
    · exact (continuous_const.mul (continuous_finset_prod _ fun i _ =>
        ((continuous_const.add (continuous_const.mul continuous_id)).sub
          continuous_const))).continuousAt
    · rw [hF0]
      exact (Finset.mem_filter.1 hj).2
  obtain ⟨ε, hεS, hεpos⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have hεpos : (0 : ℝ) < ε := hεpos
  -- the distinct case at `ε`
  have hmonoε : StrictMono fun i : Fin L => r i + (i.val : ℝ) * ε := fun i j hij =>
    add_lt_add_of_le_of_lt (hmono hij.le)
      (mul_lt_mul_of_pos_right (Nat.cast_lt.2 hij) hεpos)
  have hcount := firstRow_count_distinct hL _ (Fε ε) hmonoε
    (fun i => lt_add_of_lt_of_nonneg (hr i) (mul_nonneg (Nat.cast_nonneg _) hεpos.le))
    (mul_ne_zero (rootProduct_monic _).ne_zero hQ0) (dvd_mul_right _ _)
  rw [hlc] at hcount
  refine hcount.trans (Finset.card_le_card fun j hj => ?_)
  rw [Finset.mem_filter, hdeg] at hj
  rw [Finset.mem_filter, ← hT0]
  refine ⟨hj.1, not_lt.1 fun hlt => ?_⟩
  exact absurd hj.2 (not_le.2 (hεS j (Finset.mem_filter.2 ⟨hj.1, hlt⟩)))

end CoefficientMass
