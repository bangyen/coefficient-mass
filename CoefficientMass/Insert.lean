/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDefs

/-!
# An Insertion Reverses the Later Signs

This module proves Lemma 4.2 of `coefficient-mass-rows.tex`.  The insertion
`ins(Z, c) = {z ∈ Z : z < c} ∪ {c} ∪ {z + 1 : z ∈ Z, z ≥ c}` keeps the elements below `c`,
adds `c` and shifts the rest up by one.  For `σ ∉ Z` the factor `1 - σ/z` of `r_Z(σ)` is
negative exactly when `z < σ`, so `r_Z(σ)` has the sign `(-1)^{|Z ∩ [1, σ - 1]|}`; for
`σ > c` outside both sets the two counts differ by one.

## Definitions

* `ins`.
* `InsFlip`.

## Theorems

* `confPoly_sign`.
* `ins_filter_lt`.
* `mem_ins_self`.
* `card_ins`.
* `card_ins_filter_lt`.
* `insFlip`.
-/

namespace CoefficientMass

/-- `ins(Z, c) = {z ∈ Z : z < c} ∪ {c} ∪ {z + 1 : z ∈ Z, z ≥ c}`. -/
def ins (Z : Finset ℕ) (c : ℕ) : Finset ℕ :=
  Z.filter (· < c) ∪ insert c ((Z.filter (c ≤ ·)).image (· + 1))

/-- Lemma 4.2 of `coefficient-mass-rows.tex`: for finite `W ⊂ ℕ_{>0}` and `h ∈ ℕ_{>0} \ W`,
`W' = ins(W, h)` agrees with `W` below `h`, contains `h` and has `|W'| = |W| + 1`, and
`r_W(σ) r_{W'}(σ) < 0` for every integer `σ > h` outside `W ∪ W'`. -/
def InsFlip : Prop :=
  ∀ (W : Finset ℕ) (h : ℕ), 0 ∉ W → 0 < h → h ∉ W →
    (ins W h).filter (· < h) = W.filter (· < h) ∧ h ∈ ins W h ∧
      (ins W h).card = W.card + 1 ∧
      ∀ σ : ℕ, h < σ → σ ∉ W → σ ∉ ins W h → confPoly W σ * confPoly (ins W h) σ < 0

/-- `(-1)^{|Z ∩ [1, σ - 1]|} r_Z(σ) > 0` for `σ ∉ Z`. -/
theorem confPoly_sign {Z : Finset ℕ} (h0 : 0 ∉ Z) {σ : ℕ} (hσ : σ ∉ Z) :
    0 < (-1 : ℝ) ^ (Z.filter (· < σ)).card * confPoly Z σ := by
  classical
  rw [confPoly, ← Finset.prod_filter_mul_prod_filter_not Z (· < σ), ← mul_assoc,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine mul_pos (Finset.prod_pos fun z hz => ?_) (Finset.prod_pos fun z hz => ?_)
  · obtain ⟨hzZ, hzσ⟩ := Finset.mem_filter.1 hz
    have hz0 : (0 : ℝ) < z := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hzZ)
    have : (z : ℝ) < σ := by exact_mod_cast hzσ
    have : 1 < (σ : ℝ) / z := by rw [one_lt_div hz0]; exact this
    linarith
  · obtain ⟨hzZ, hzσ⟩ := Finset.mem_filter.1 hz
    have hz0 : (0 : ℝ) < z := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hzZ)
    have : (σ : ℝ) < z := by
      exact_mod_cast lt_of_le_of_ne (not_lt.1 hzσ) fun h => hσ (h ▸ hzZ)
    have : (σ : ℝ) / z < 1 := by rw [div_lt_one hz0]; exact this
    linarith

theorem ins_filter_lt (W : Finset ℕ) (h : ℕ) : (ins W h).filter (· < h) = W.filter (· < h) := by
  ext x
  simp only [ins, Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hx | rfl | ⟨w, ⟨hw, hhw⟩, rfl⟩, hxh⟩
    · exact hx
    · exact absurd hxh (lt_irrefl _)
    · omega
  · rintro ⟨hx, hxh⟩
    exact ⟨Or.inl ⟨hx, hxh⟩, hxh⟩

theorem mem_ins_self (W : Finset ℕ) (h : ℕ) : h ∈ ins W h :=
  Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem card_ins {W : Finset ℕ} {h : ℕ} (hW : h ∉ W) : (ins W h).card = W.card + 1 := by
  classical
  have hdisj : Disjoint (W.filter (· < h)) (insert h ((W.filter (h ≤ ·)).image (· + 1))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := (Finset.mem_filter.1 hx).2
    rcases Finset.mem_insert.1 hx' with rfl | hx'
    · exact lt_irrefl _ this
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx'
      have := (Finset.mem_filter.1 hw).2
      omega
  have hnot : h ∉ (W.filter (h ≤ ·)).image (· + 1) := fun hh => by
    obtain ⟨w, hw, hwh⟩ := Finset.mem_image.1 hh
    have := (Finset.mem_filter.1 hw).2
    omega
  rw [ins, Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (add_left_injective 1)]
  have := Finset.card_filter_add_card_filter_not (s := W) (· < h)
  have hfe : W.filter (h ≤ ·) = W.filter (fun x => ¬ x < h) :=
    Finset.filter_congr fun x _ => not_lt.symm
  rw [hfe]
  omega

/-- Below `σ > h`, with `σ ∉ W ∪ ins(W, h)`, the insertion adds exactly one element. -/
theorem card_ins_filter_lt {W : Finset ℕ} {h σ : ℕ} (hW : h ∉ W) (hσ : h < σ)
    (hσW' : σ ∉ ins W h) :
    ((ins W h).filter (· < σ)).card = (W.filter (· < σ)).card + 1 := by
  classical
  have hσ1 : σ - 1 ∉ W := fun hw => hσW' (Finset.mem_union_right _ (Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨σ - 1, Finset.mem_filter.2 ⟨hw, by omega⟩, by omega⟩)))
  -- the two sets below `σ`, as images of `W` below `σ` with `h` added
  have hsplit : (ins W h).filter (· < σ) =
      insert h ((W.filter (· < σ)).image fun w => if w < h then w else w + 1) := by
    ext x
    simp only [ins, Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨(⟨hx, hxh⟩ | rfl | ⟨w, ⟨hw, hhw⟩, rfl⟩), hxσ⟩
      · exact Or.inr ⟨x, ⟨hx, by omega⟩, if_pos hxh⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨w, ⟨hw, by omega⟩, ?_⟩
        rw [if_neg (by omega)]
    · rintro (rfl | ⟨w, ⟨hw, hwσ⟩, rfl⟩)
      · exact ⟨Or.inr (Or.inl rfl), hσ⟩
      · by_cases hwh : w < h
        · rw [if_pos hwh]
          exact ⟨Or.inl ⟨hw, hwh⟩, hwσ⟩
        · rw [if_neg hwh]
          have hwσ' : w ≠ σ - 1 := fun h' => hσ1 (h' ▸ hw)
          exact ⟨Or.inr (Or.inr ⟨w, ⟨hw, not_lt.1 hwh⟩, rfl⟩), by omega⟩
  have hinj : Set.InjOn (fun w => if w < h then w else w + 1) (W.filter (· < σ) : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    have ha' := (Finset.mem_filter.1 ha).1
    have hb' := (Finset.mem_filter.1 hb).1
    split_ifs at hab <;> omega
  have hnot : h ∉ (W.filter (· < σ)).image fun w => if w < h then w else w + 1 := fun hh => by
    obtain ⟨w, hw, hwh⟩ := Finset.mem_image.1 hh
    have hwW := (Finset.mem_filter.1 hw).1
    split_ifs at hwh with h1
    · exact hW (hwh ▸ hwW)
    · have : w + 1 = h := hwh
      have : h ≤ w := not_lt.1 h1
      omega
  rw [hsplit, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]

theorem insFlip : InsFlip := by
  intro W h h0 hh hW
  refine ⟨ins_filter_lt W h, mem_ins_self W h, card_ins hW, fun σ hσ hσW hσW' => ?_⟩
  have h0' : 0 ∉ ins W h := fun h' => by
    simp only [ins, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_image] at h'
    rcases h' with ⟨h', _⟩ | h' | ⟨w, _, hw⟩
    · exact h0 h'
    · omega
    · omega
  have s1 := confPoly_sign h0 hσW
  have s2 := confPoly_sign h0' hσW'
  rw [card_ins_filter_lt hW hσ hσW', pow_succ] at s2
  have hsq : ((-1 : ℝ) ^ (W.filter (· < σ)).card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hprod : confPoly W σ * confPoly (ins W h) σ =
      -(((-1 : ℝ) ^ (W.filter (· < σ)).card * confPoly W σ) *
        ((-1 : ℝ) ^ (W.filter (· < σ)).card * -1 * confPoly (ins W h) σ)) := by
    linear_combination (-(confPoly W σ * confPoly (ins W h) σ)) * hsq
  rw [hprod]
  linarith [mul_pos s1 s2]

end CoefficientMass
