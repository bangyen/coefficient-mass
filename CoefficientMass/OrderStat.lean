/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Order
import CoefficientMass.Perturb
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.OrderClosed

/-!
# Coefficient Order Statistics

This module proves Theorem 3.2 of `coefficient-mass.tex` from Lemma 3.1.  For
distinct roots and `|f_D| = 1`, a set `U` of fewer than `u + 1` large
positions is excluded by the lemma; dividing by `f_D` handles any leading
coefficient; and repeated roots are moved apart to `r_i + i ε`, whose
coefficients and thresholds tend to those at `ε = 0`.

## Theorems

* `one_le_prod_sub_one`.
* `count_of_certificate`.
* `count_of_distinct`.
* `orderStatistics_of_certificate`.
-/

open Polynomial Topology

namespace CoefficientMass

theorem one_le_prod_sub_one {L : ℕ} (r : Fin L → ℝ) (hr : ∀ i, 2 ≤ r i)
    (s : Finset (Fin L)) : 1 ≤ ∏ i ∈ s, (r i - 1) :=
  Finset.prod_induction _ (1 ≤ ·) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun i _ => by linarith [hr i]

/-- The distinct, normalized case: Lemma 3.1 with `U` the large positions. -/
theorem count_of_certificate (hc : CertificateWithExclusions) {L : ℕ} (r : Fin L → ℝ)
    (G : ℝ[X]) (hmono : StrictMono r) (hr : ∀ i, 2 ≤ r i) (hdvd : rootProduct ℝ r ∣ G)
    (hlead : ‖G.leadingCoeff‖ = 1) (u : Fin L) :
    u.val + 1 ≤ largeCount G (∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1)) := by
  classical
  by_contra hlt
  rw [not_le, Nat.lt_succ_iff] at hlt
  set T := ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1) with hT
  set U := (Finset.range G.natDegree).filter fun j => T ≤ ‖G.coeff j‖ with hU
  have hUc : U.card ≤ u.val := hlt
  obtain ⟨j, hjD, hjU, hjT⟩ := hc L r G U hmono hr hdvd hlead (by
    have := u.isLt
    omega) (Finset.filter_subset _ _)
  have hsub : Finset.univ.filter (u ≤ ·) ⊆ Finset.univ.filter fun i : Fin L => U.card ≤ i.val :=
    fun i hi => by
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      have := Fin.le_def.1 hi.2
      omega
  have hle : T ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin L => U.card ≤ i.val), (r i - 1) := by
    rw [← Finset.prod_sdiff hsub, ← hT]
    exact le_mul_of_one_le_left (hT ▸ zero_le_one.trans (one_le_prod_sub_one r hr _))
      (one_le_prod_sub_one r hr _)
  exact hjU (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjD, hle.trans hjT⟩)

/-- The distinct case for any leading coefficient. -/
theorem count_of_distinct (hc : CertificateWithExclusions) {L : ℕ} (r : Fin L → ℝ)
    (G : ℝ[X]) (hmono : StrictMono r) (hr : ∀ i, 2 ≤ r i) (hG : G ≠ 0)
    (hdvd : rootProduct ℝ r ∣ G) (u : Fin L) :
    u.val + 1 ≤ largeCount G
      (‖G.leadingCoeff‖ * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1)) := by
  have hc0 : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hG
  have hn : 0 < ‖G.leadingCoeff‖ := norm_pos_iff.2 hc0
  have h := count_of_certificate hc r (C G.leadingCoeff⁻¹ * G) hmono hr
    (dvd_mul_of_dvd_right hdvd _) (by
      rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hc0, norm_one]) u
  refine h.trans (le_of_eq ?_)
  rw [largeCount, largeCount, natDegree_C_mul (inv_ne_zero hc0)]
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  rw [coeff_C_mul, norm_mul, norm_inv, mul_comm ‖G.leadingCoeff‖, ← le_div_iff₀ hn,
    div_eq_inv_mul]

/-- Theorem 3.2 from Lemma 3.1. -/
theorem orderStatistics_of_certificate (hc : CertificateWithExclusions) : OrderStatistics := by
  classical
  intro L r F hmono hr hF hdvd u
  obtain ⟨Q, hQ⟩ := hdvd
  have hQ0 : Q ≠ 0 := fun h => hF (by rw [hQ, h, mul_zero])
  set Fε : ℝ → ℝ[X] := fun ε => rootProduct ℝ (fun i => r i + (i.val : ℝ) * ε) * Q with hFε
  set Tε : ℝ → ℝ := fun ε => ‖F.leadingCoeff‖ *
    ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i + (i.val : ℝ) * ε - 1) with hTε
  have hF0 : Fε 0 = F := by
    simp only [hFε, mul_zero, add_zero]
    exact hQ.symm
  have hT0 : Tε 0 = ‖F.leadingCoeff‖ * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1) := by
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
  have hcount := count_of_distinct hc _ (Fε ε) hmonoε
    (fun i => le_add_of_le_of_nonneg (hr i) (mul_nonneg (Nat.cast_nonneg _) hεpos.le))
    (mul_ne_zero (rootProduct_monic _).ne_zero hQ0)
    (dvd_mul_right _ _) u
  rw [hlc] at hcount
  refine hcount.trans (Finset.card_le_card fun j hj => ?_)
  rw [Finset.mem_filter, hdeg] at hj
  rw [Finset.mem_filter, ← hT0]
  refine ⟨hj.1, not_lt.1 fun hlt => ?_⟩
  exact absurd hj.2 (not_le.2 (hεS j (Finset.mem_filter.2 ⟨hj.1, hlt⟩)))

end CoefficientMass
