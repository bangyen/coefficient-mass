/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.DisplacedGen
import CoefficientMass.Tail

/-!
# The Tail Bound at Arbitrary Nodes

This module proves Theorem 2.2 of `coefficient-mass-rows.tex`: for nodes
`0 < y_1 < ⋯ < y_c < 1`, a zero set `Z ⊆ ℕ_{>0}` of size `c - 1` and any `ℓ` with
`{1, …, ℓ} ⊆ Z`, the tail is at most `∏_{i ≤ ℓ+1} φ_i ∏_{i > ℓ+1} max(1, φ_i)` with
`φ_i = y_i / (1 - y_i)`.  The induction is that of Theorem 2.2 of `coefficient-mass.tex`,
with the displaced step `tsum_le_of_displaced_gen`.

## Definitions

* `TailBoundGen`.

## Theorems

* `prod_max_castSucc`.
* `tailBoundGen`.
-/

namespace CoefficientMass

/-- Theorem 2.2 of `coefficient-mass-rows.tex` (tail bound at arbitrary nodes). -/
def TailBoundGen : Prop :=
  ∀ (c : ℕ) (a y : Fin c → ℝ) (Z : Finset ℕ) (ℓ : ℕ),
    StrictMono y → (∀ i, 0 < y i) → (∀ i, y i < 1) →
    0 ∉ Z → Z.card = c - 1 → Finset.Icc 1 ℓ ⊆ Z → IsCertificate a y Z →
      ∑' d, |expSum a y (d + 1)| ≤ nodeProduct y ℓ *
        ∏ i ∈ Finset.univ.filter (fun i : Fin c => ℓ < i.val), max 1 (y i / (1 - y i))

theorem prod_max_castSucc {n : ℕ} (y : Fin (n + 1) → ℝ) {ℓ : ℕ} (hℓ : ℓ < n) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => ℓ < i.val), max 1 (y i / (1 - y i)) =
      max 1 (y (Fin.last n) / (1 - y (Fin.last n))) *
        ∏ i ∈ Finset.univ.filter (fun i : Fin n => ℓ < i.val),
          max 1 (y i.castSucc / (1 - y i.castSucc)) := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [if_pos hℓ, mul_comm]

/-- Theorem 2.2 of `coefficient-mass-rows.tex`. -/
theorem tailBoundGen : TailBoundGen := by
  intro c
  induction c with
  | zero =>
    intro a y Z ℓ _ _ _ _ _ _ ha
    have h1 := ha.1
    simp only [expSum, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 zero_ne_one
  | succ n ih =>
    intro a y Z ℓ hmono hpos hlt1 h0 hcard hℓ ha
    rw [Nat.add_sub_cancel] at hcard
    have hφ : ∀ i, 0 ≤ y i / (1 - y i) := fun i =>
      div_nonneg (hpos i).le (by linarith [hlt1 i])
    have hmax0 : ∀ i, 0 ≤ max 1 (y i / (1 - y i)) := fun i =>
      le_trans zero_le_one (le_max_left _ _)
    have hIoo : ∀ τ, τ ∈ Finset.Ioo 0 (n + 1) ↔ 1 ≤ τ ∧ τ ≤ n := fun τ => by
      rw [Finset.mem_Ioo]
      omega
    have hIoocard : (Finset.Ioo 0 (n + 1)).card = n := by rw [Nat.card_Ioo]; omega
    have hℓn : ℓ ≤ n := by
      by_contra hle
      push_neg at hle
      have := Finset.card_le_card (show Finset.Icc 1 (n + 1) ⊆ Z from fun τ hτ =>
        hℓ (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hτ).1, by have := (Finset.mem_Icc.1 hτ).2; omega⟩))
      rw [Nat.card_Icc, hcard] at this
      omega
    by_cases hZ : Z = Finset.Ioo 0 (n + 1)
    · subst hZ
      have h := consecutiveTail (n + 1) a y hmono hpos hlt1 ha
      rw [h.tsum_eq, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : Fin (n + 1) => i.val ≤ ℓ)]
      have hnot : Finset.univ.filter (fun i : Fin (n + 1) => ¬ i.val ≤ ℓ) =
          Finset.univ.filter (fun i : Fin (n + 1) => ℓ < i.val) :=
        Finset.filter_congr fun i _ => not_le
      rw [hnot, nodeProduct]
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => hφ i)
        fun i _ => le_max_right _ _) (Finset.prod_nonneg fun i _ => hφ i)
    have hne : Z.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      refine hZ (Finset.eq_empty_of_forall_notMem fun τ hτ => ?_).symm
      rw [Finset.card_empty] at hcard
      have := (hIoo τ).1 hτ
      omega
    set z := Z.max' hne
    have hz : z ∈ Z := Z.max'_mem hne
    have hzmax : ∀ τ ∈ Z, τ ≤ z := fun τ hτ => Z.le_max' τ hτ
    have hℓlt : ℓ < n := by
      rcases hℓn.lt_or_eq with h | h
      · exact h
      refine absurd (Finset.eq_of_subset_of_card_le (fun τ hτ => hℓ ?_) ?_).symm hZ
      · have := (hIoo τ).1 hτ
        exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · rw [hIoocard, hcard]
    set Z' := Z.erase z
    have h0' : 0 ∉ Z' := fun h => h0 (Finset.mem_of_mem_erase h)
    have hZ'card : Z'.card = n - 1 := by rw [Finset.card_erase_of_mem hz, hcard]
    have hzn : n + 1 ≤ z := by
      by_contra hlt
      push_neg at hlt
      refine hZ (Finset.eq_of_subset_of_card_le (fun τ hτ => (hIoo τ).2 ⟨?_, ?_⟩) ?_)
      · exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hτ)
      · have := hzmax τ hτ
        omega
      · rw [hIoocard, hcard]
    have hℓ' : Finset.Icc 1 ℓ ⊆ Z' := fun τ hτ => by
      have := Finset.mem_Icc.1 hτ
      exact Finset.mem_erase.2 ⟨by omega, hℓ hτ⟩
    have hmono' : StrictMono fun i : Fin n => y i.castSucc :=
      fun i j h => hmono (Fin.castSucc_lt_castSucc_iff.2 h)
    obtain ⟨aF, hF⟩ := exists_certificate zeroBound (fun i : Fin n => y i.castSucc)
      hmono'.injective (fun i => hpos _) Z' h0' (by
        have := Finset.card_pos.2 ⟨z, hz⟩
        omega)
    have hFs := summable_tail aF (fun i : Fin n => y i.castSucc) (fun i => hpos _)
      fun i => hlt1 _
    have hFb := ih aF (fun i => y i.castSucc) Z' ℓ hmono' (fun i => hpos _)
      (fun i => hlt1 _) h0' hZ'card hℓ' hF
    calc ∑' d, |expSum a y (d + 1)|
        ≤ max 1 (y (Fin.last n) / (1 - y (Fin.last n))) *
            ∑' d, |expSum aF (fun i => y i.castSucc) (d + 1)| :=
          tsum_le_of_displaced_gen y hmono hpos hlt1 Z hz hzmax h0 hcard a ha aF hF hFs
      _ ≤ max 1 (y (Fin.last n) / (1 - y (Fin.last n))) *
            (nodeProduct (fun i => y i.castSucc) ℓ *
              ∏ i ∈ Finset.univ.filter (fun i : Fin n => ℓ < i.val),
                max 1 (y i.castSucc / (1 - y i.castSucc))) :=
          mul_le_mul_of_nonneg_left hFb (hmax0 _)
      _ = nodeProduct y ℓ *
            ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => ℓ < i.val),
              max 1 (y i / (1 - y i)) := by
          rw [nodeProduct_castSucc y hℓlt, prod_max_castSucc y hℓlt]
          ring

end CoefficientMass
