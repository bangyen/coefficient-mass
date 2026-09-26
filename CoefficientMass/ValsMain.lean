/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ValsSum

/-!
# The Values at the Kept Holes

This module proves Lemma 4.10 of `coefficient-mass.tex` for `q ≥ 1`.  At the `r`-th kept
hole `c` (from `0`), `abs_confPoly_split` and the product bounds give
`2^{-c} |ψ(c)| ≤ W_r(c)`, which is at most the block value at `ℓ + 1 + r`; the rank
`c ↦ r` is a bijection onto `{0, …, ℓ}`, so the sum is at most `1 / (2(q + 1))`.

## Definitions

* `HoleVals`.

## Theorems

* `hole_value_le`.
* `rank_lt`.
* `holeVals`.
-/

namespace CoefficientMass

/-- Lemma 4.10: for `C = {c_1 < ⋯ < c_{ℓ+1}}` with `c_1 = ℓ + 1`, `C ⊆ [ℓ + 1, m]`,
`N = m + q`, `q ≥ 1` and `Y = {1, …, N} \ C`, `∑_{c ∈ C} |r_Y(c)| 2^{-c} ≤ 1 / (2(q + 1))`. -/
def HoleVals : Prop :=
  ∀ (ℓ q m : ℕ) (C : Finset ℕ), 1 ≤ q → C.card = ℓ + 1 → ℓ + 1 ∈ C →
    (∀ c ∈ C, ℓ + 1 ≤ c ∧ c ≤ m) →
    ∑ c ∈ C, |confPoly (Finset.Icc 1 (m + q) \ C) c| * (1 / 2 : ℝ) ^ c ≤
      1 / (2 * ((q : ℝ) + 1))
/-- The bound at one kept hole `c` of rank `r = |{c' ∈ C : c' < c}|`. -/
theorem hole_value_le {ℓ q m : ℕ} {C : Finset ℕ} (hC : C.card = ℓ + 1) (hl : ℓ + 1 ∈ C)
    (hCm : ∀ c ∈ C, ℓ + 1 ≤ c ∧ c ≤ m) {c : ℕ} (hc : c ∈ C) :
    |confPoly (Finset.Icc 1 (m + q) \ C) c| * (1 / 2 : ℝ) ^ c ≤
      blockCoef ℓ (C.filter (· < c)).card *
        betaI (ℓ - (C.filter (· < c)).card + q) (ℓ + (C.filter (· < c)).card) := by
  have h1 := below_card (fun x hx => (hCm x hx).1) (hCm c hc).1
  have h2 := above_card hC hc
  have h3 := top_bound (c := c) (fun x hx => (hCm x hx).2) (hCm c hc).2
  have hL0 : 0 ≤ ∏ x ∈ C.filter (· < c), ((x : ℝ) / ((c : ℝ) - x)) :=
    Finset.prod_nonneg fun x hx => by
      have : (x : ℝ) < c := by exact_mod_cast (Finset.mem_filter.1 hx).2
      exact div_nonneg (Nat.cast_nonneg x) (by linarith)
  have hU0 : 0 ≤ ∏ x ∈ C.filter (c < ·), ((x : ℝ) / ((x : ℝ) - c)) :=
    Finset.prod_nonneg fun x hx => by
      have : (c : ℝ) < x := by exact_mod_cast (Finset.mem_filter.1 hx).2
      exact div_nonneg (Nat.cast_nonneg x) (by linarith)
  have hU := prod_up_le c _ fun x hx => (Finset.mem_filter.1 hx).2
  have hsplit := abs_confPoly_split (N := m + q) (fun h0 => by have := (hCm 0 h0).1; omega)
    (fun x hx => by have := (hCm x hx).2; omega) hc
  rw [hsplit]
  obtain ⟨r, hr⟩ : ∃ r, (C.filter (· < c)).card = r := ⟨_, rfl⟩
  rw [hr] at h1 h2 ⊢
  rw [show (C.filter (c < ·)).card = ℓ - r by omega] at hU
  have hβ : betaI (m + q - c) (c - 1) ≤ betaI (ℓ - r + q) (c - 1) := betaI_anti (by omega) _
  rcases r with _ | s
  · have hcl : c = ℓ + 1 := by
      by_contra hne
      have hmem : ℓ + 1 ∈ C.filter (· < c) :=
        Finset.mem_filter.2 ⟨hl, by have := (hCm c hc).1; omega⟩
      have := Finset.card_pos.2 ⟨_, hmem⟩
      omega
    rw [Finset.card_eq_zero.1 hr, Finset.prod_empty]
    subst hcl
    rw [Nat.add_sub_cancel] at hβ ⊢
    refine (mul_bound (by positivity) (Nat.cast_nonneg _) hβ (betaI_nonneg _ _) le_rfl
      zero_le_one hU hU0).trans_eq ?_
    rw [mul_one]
    exact hole_zero_block ℓ q
  · have hs : s + 1 ≤ ℓ := by omega
    have hmem : ℓ + 1 ∈ C.filter (· < c) := Finset.mem_filter.2 ⟨hl, by omega⟩
    have hA : ((ℓ + 1 : ℕ) : ℝ) / ((c : ℝ) - ((ℓ + 1 : ℕ) : ℝ)) =
        ((ℓ : ℝ) + 1) / ((c : ℝ) - ℓ - 1) := by
      push_cast
      rw [sub_add_eq_sub_sub]
    have hcl : (ℓ : ℝ) + 1 + 1 ≤ c := by exact_mod_cast (show ℓ + 1 + 1 ≤ c by omega)
    have hP := prod_down_le (c := c) (by omega) ((C.filter (· < c)).erase (ℓ + 1))
      fun x hx => (Finset.mem_filter.1 (Finset.mem_of_mem_erase hx)).2
    rw [Finset.card_erase_of_mem hmem, hr, Nat.add_sub_cancel] at hP
    have hL : ∏ x ∈ C.filter (· < c), ((x : ℝ) / ((c : ℝ) - x)) ≤
        ((ℓ : ℝ) + 1) / ((c : ℝ) - ℓ - 1) * pDown s c := by
      rw [← Finset.mul_prod_erase _ _ hmem, hA]
      exact mul_le_mul_of_nonneg_left hP (div_nonneg (by positivity) (by linarith))
    have hW := holeW_le (q := q) (by omega : 1 ≤ s + 1) hs (c - (ℓ + 1 + (s + 1)))
    rw [show ℓ + 1 + (s + 1) + (c - (ℓ + 1 + (s + 1))) = c by omega, holeW_block hs] at hW
    refine le_trans ?_ hW
    refine (mul_bound (by positivity) (Nat.cast_nonneg _) hβ (betaI_nonneg _ _) hL hL0 hU
      hU0).trans_eq ?_
    rw [holeW, Nat.add_sub_cancel]

theorem rank_lt {C : Finset ℕ} {x y : ℕ} (hx : x ∈ C) (hxy : x < y) :
    (C.filter (· < x)).card < (C.filter (· < y)).card := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun z hz => ?_).2
    ⟨x, Finset.mem_filter.2 ⟨hx, hxy⟩, fun h => lt_irrefl x (Finset.mem_filter.1 h).2⟩)
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, (Finset.mem_filter.1 hz).2.trans hxy⟩

theorem holeVals : HoleVals := by
  intro ℓ q m C hq hC hl hCm
  set rk : ℕ → ℕ := fun c => (C.filter (· < c)).card with hrk
  have inj : Set.InjOn rk C := by
    intro x hx y hy h
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd h (rank_lt hx hxy).ne
    · exact hxy
    · exact absurd h (rank_lt hy hxy).ne'
  have himg : C.image rk = Finset.range (ℓ + 1) := by
    refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
      have := above_card hC hc
      exact Finset.mem_range.2 (show (C.filter (· < c)).card < ℓ + 1 by omega)
    · rw [Finset.card_range, Finset.card_image_of_injOn inj, hC]
  calc ∑ c ∈ C, |confPoly (Finset.Icc 1 (m + q) \ C) c| * (1 / 2 : ℝ) ^ c
      ≤ ∑ c ∈ C, blockCoef ℓ (rk c) * betaI (ℓ - rk c + q) (ℓ + rk c) :=
        Finset.sum_le_sum fun c hc => hole_value_le hC hl hCm hc
    _ = ∑ r ∈ C.image rk, blockCoef ℓ r * betaI (ℓ - r + q) (ℓ + r) :=
        (Finset.sum_image inj).symm
    _ ≤ 1 / (2 * ((q : ℝ) + 1)) := by
        rw [himg]
        exact block_le ℓ hq

end CoefficientMass
