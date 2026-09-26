/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LooseRow

/-!
# Unbounded Looseness of the First Row

This module proves Proposition 4.1 of `coefficient-mass.tex`: for real roots
`1 < r_1 ≤ ⋯ ≤ r_L`, repetitions allowed, every nonzero multiple `F` of `∏ (x - r_i)` has
`b_1(F) ≥ |f_D| S B / (B + 1)` with `S = ∑ r_i` and `B = ∏ (r_i - 1)`; repeated roots are
moved apart as in Theorem 3.2.  For `r_i ≥ 2`, `B ≥ 1` gives the bound (4.3),
`b_1(F) ≥ S / 2` for monic `F`.

## Definitions

* `UnboundedLooseness`.
* `HalfSum`.

## Theorems

* `unboundedLooseness`.
* `halfSum`.
-/

open Polynomial Topology

namespace CoefficientMass

/-- Proposition 4.1: `b_1(F) ≥ |f_D| S B / (B + 1)` for real roots `1 < r_1 ≤ ⋯ ≤ r_L`,
`S = ∑ r_i`, `B = ∏ (r_i - 1)`. -/
def UnboundedLooseness : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), 0 < L → Monotone r → (∀ i, 1 < r i) → F ≠ 0 →
    rootProduct ℝ r ∣ F → 1 ≤ largeCount F (‖F.leadingCoeff‖ *
      ((∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1)))

/-- The bound (4.3) of Proposition 4.1: `b_1(F) ≥ (r_1 + ⋯ + r_L) / 2` for a monic
multiple `F` of `∏ (x - r_i)` with `2 ≤ r_1 ≤ ⋯ ≤ r_L`. -/
def HalfSum : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), 0 < L → Monotone r → (∀ i, 2 ≤ r i) → F.Monic →
    rootProduct ℝ r ∣ F → 1 ≤ largeCount F ((∑ i, r i) / 2)

/-- Proposition 4.1. -/
theorem unboundedLooseness : UnboundedLooseness := by
  classical
  intro L r F hL hmono hr hF hdvd
  obtain ⟨Q, hQ⟩ := hdvd
  have hQ0 : Q ≠ 0 := fun h => hF (by rw [hQ, h, mul_zero])
  set Fε : ℝ → ℝ[X] := fun ε => rootProduct ℝ (fun i => r i + (i.val : ℝ) * ε) * Q with hFε
  set Tε : ℝ → ℝ := fun ε => ‖F.leadingCoeff‖ * ((∑ i, (r i + (i.val : ℝ) * ε)) *
    (∏ i, (r i + (i.val : ℝ) * ε - 1)) / (∏ i, (r i + (i.val : ℝ) * ε - 1) + 1)) with hTε
  have hF0 : Fε 0 = F := by
    simp only [hFε, mul_zero, add_zero]
    exact hQ.symm
  have hT0 : Tε 0 = ‖F.leadingCoeff‖ *
      ((∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1)) := by
    simp only [hTε, mul_zero, add_zero]
  have hdeg : ∀ ε, (Fε ε).natDegree = F.natDegree := fun ε => by
    rw [hQ, hFε, natDegree_mul (rootProduct_monic _).ne_zero hQ0,
      natDegree_mul (rootProduct_monic _).ne_zero hQ0, natDegree_rootProduct,
      natDegree_rootProduct]
  have hlc : ∀ ε, (Fε ε).leadingCoeff = F.leadingCoeff := fun ε => by
    rw [hQ, hFε, leadingCoeff_mul, leadingCoeff_mul, (rootProduct_monic _).leadingCoeff,
      (rootProduct_monic _).leadingCoeff]
  have hc1 : Continuous fun ε : ℝ => ∑ i, (r i + (i.val : ℝ) * ε) :=
    continuous_finset_sum _ fun i _ => continuous_const.add (continuous_const.mul continuous_id)
  have hc2 : Continuous fun ε : ℝ => ∏ i, (r i + (i.val : ℝ) * ε - 1) :=
    continuous_finset_prod _ fun i _ =>
      (continuous_const.add (continuous_const.mul continuous_id)).sub continuous_const
  have hne : (∏ i, (r i + (i.val : ℝ) * 0 - 1)) + 1 ≠ 0 := by
    simp only [mul_zero, add_zero]
    exact (add_pos (Finset.prod_pos fun i _ => by linarith [hr i]) one_pos).ne'
  have hTc : ContinuousAt Tε 0 :=
    continuousAt_const.mul ((hc1.mul hc2).continuousAt.div
      (hc2.add continuous_const).continuousAt hne)
  -- the positions that are small at `ε = 0` stay small for small `ε`
  set S := (Finset.range F.natDegree).filter fun j => ‖F.coeff j‖ < Tε 0 with hS
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j ∈ S, ‖(Fε ε).coeff j‖ < Tε ε := by
    refine (Filter.eventually_all_finset S).2 fun j hj => ?_
    refine ContinuousAt.eventually_lt ?_ hTc ?_
    · exact (continuous_norm.comp (continuous_coeff_rootProduct_mul r Q j)).continuousAt
    · rw [hF0]
      exact (Finset.mem_filter.1 hj).2
  obtain ⟨ε, hεS, hεpos⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have hεpos : (0 : ℝ) < ε := hεpos
  -- the distinct case at `ε`
  have hmonoε : StrictMono fun i : Fin L => r i + (i.val : ℝ) * ε := fun i j hij =>
    add_lt_add_of_le_of_lt (hmono hij.le)
      (mul_lt_mul_of_pos_right (Nat.cast_lt.2 hij) hεpos)
  have hcount := loose_count_distinct hL _ (Fε ε) hmonoε
    (fun i => lt_add_of_lt_of_nonneg (hr i) (mul_nonneg (Nat.cast_nonneg _) hεpos.le))
    (mul_ne_zero (rootProduct_monic _).ne_zero hQ0) (dvd_mul_right _ _)
  rw [hlc] at hcount
  refine hcount.trans (Finset.card_le_card fun j hj => ?_)
  rw [Finset.mem_filter, hdeg] at hj
  rw [Finset.mem_filter, ← hT0]
  refine ⟨hj.1, not_lt.1 fun hlt => ?_⟩
  exact absurd hj.2 (not_le.2 (hεS j (Finset.mem_filter.2 ⟨hj.1, hlt⟩)))

/-- The bound (4.3): `B ≥ 1` for `r_i ≥ 2`, so `S B / (B + 1) ≥ S / 2`. -/
theorem halfSum : HalfSum := by
  intro L r F hL hmono hr hF hdvd
  have h := unboundedLooseness L r F hL hmono (fun i => by linarith [hr i]) hF.ne_zero hdvd
  rw [hF.leadingCoeff, norm_one, one_mul] at h
  have hB : 1 ≤ ∏ i, (r i - 1) := by
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ))
      (fun _ _ => zero_le_one) fun i _ => (by linarith [hr i] : (1 : ℝ) ≤ r i - 1)
    rwa [Finset.prod_const_one] at this
  have hS : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => by linarith [hr i]
  have hle : (∑ i, r i) / 2 ≤ (∑ i, r i) * (∏ i, (r i - 1)) / (∏ i, (r i - 1) + 1) := by
    rw [div_le_div_iff₀ two_pos (by linarith)]
    nlinarith
  exact h.trans (Finset.card_le_card fun j hj => Finset.mem_filter.2
    ⟨(Finset.mem_filter.1 hj).1, hle.trans (Finset.mem_filter.1 hj).2⟩)

end CoefficientMass
