/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Chain

/-!
# The Equality Case of the Tail Bound

This module proves the equality clause of Theorem 2.2 of
`coefficient-mass.tex`: with `ℓ` the leading run, the tail equals
`∏_{i ≤ ℓ+1} y_i / (1 - y_i)` exactly when the zero set is `{1, …, c - 1}`.
Otherwise the largest zero `z` exceeds `c - 1`, so some `1 ≤ d < z` lies
outside the zero set, and the first displaced step is strict there.

## Definitions

* `TailEquality`.

## Theorems

* `exists_gap_below_max`.
* `tsum_lt_nodeProduct`.
* `tailEquality`.
-/

namespace CoefficientMass

/-- Theorem 2.2 (equality case): for nodes `0 < y_1 < ⋯ < y_c ≤ 1/2`, a zero
set `Z ⊆ ℕ_{>0}` of size `c - 1` and its leading run `ℓ`, the tail equals
`∏_{i ≤ ℓ+1} y_i / (1 - y_i)` exactly when `Z = {1, …, c - 1}`. -/
def TailEquality : Prop :=
  ∀ (c : ℕ) (a y : Fin c → ℝ) (Z : Finset ℕ) (ℓ : ℕ),
    StrictMono y → (∀ i, 0 < y i) → (∀ i, y i ≤ 1 / 2) →
    0 ∉ Z → Z.card = c - 1 → Finset.Icc 1 ℓ ⊆ Z → ℓ + 1 ∉ Z → IsCertificate a y Z →
      (∑' d, |expSum a y (d + 1)| = nodeProduct y ℓ ↔ Z = Finset.Ioo 0 c)

/-- A zero set of size `n` whose largest element `z` exceeds `n` misses some
`1 ≤ d < z`. -/
theorem exists_gap_below_max {Z : Finset ℕ} {n z : ℕ} (hcard : Z.card = n) (hz : z ∈ Z)
    (hzn : n + 1 ≤ z) : ∃ d, 1 ≤ d ∧ d < z ∧ d ∉ Z := by
  by_contra h
  push_neg at h
  have hsub : Finset.Icc 1 z ⊆ Z := fun d hd => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hd
    rcases lt_or_eq_of_le h2 with h2 | rfl
    · exact h 1 d h1 h2
    · exact hz
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-- Away from the consecutive zero set the tail bound is strict. -/
theorem tsum_lt_nodeProduct {n : ℕ} (a y : Fin (n + 1) → ℝ) (Z : Finset ℕ) (ℓ : ℕ)
    (hmono : StrictMono y) (hpos : ∀ i, 0 < y i) (hhalf : ∀ i, y i ≤ 1 / 2) (h0 : 0 ∉ Z)
    (hcard : Z.card = n) (hℓ : Finset.Icc 1 ℓ ⊆ Z) (ha : IsCertificate a y Z)
    (hZ : Z ≠ Finset.Ioo 0 (n + 1)) :
    ∑' d, |expSum a y (d + 1)| < nodeProduct y ℓ := by
  have hIoo : ∀ τ, τ ∈ Finset.Ioo 0 (n + 1) ↔ 1 ≤ τ ∧ τ ≤ n := fun τ => by
    rw [Finset.mem_Ioo]
    omega
  have hIoocard : (Finset.Ioo 0 (n + 1)).card = n := by rw [Nat.card_Ioo]; omega
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
  have hzn : n + 1 ≤ z := by
    by_contra hlt
    push_neg at hlt
    refine hZ (Finset.eq_of_subset_of_card_le (fun τ hτ => (hIoo τ).2 ⟨?_, ?_⟩) ?_)
    · exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hτ)
    · have := hzmax τ hτ
      omega
    · rw [hIoocard, hcard]
  have hℓn : ℓ < n := by
    by_contra hle
    push_neg at hle
    refine hZ (Finset.eq_of_subset_of_card_le (fun τ hτ => hℓ ?_) ?_).symm
    · have := (hIoo τ).1 hτ
      exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
    · rw [hIoocard, hcard]
  set Z' := Z.erase z
  have h0' : 0 ∉ Z' := fun h => h0 (Finset.mem_of_mem_erase h)
  have hZ'card : Z'.card = n - 1 := by rw [Finset.card_erase_of_mem hz, hcard]
  have hℓ' : Finset.Icc 1 ℓ ⊆ Z' := fun τ hτ => by
    have := Finset.mem_Icc.1 hτ
    exact Finset.mem_erase.2 ⟨by omega, hℓ hτ⟩
  have hmono' : StrictMono fun i : Fin n => y i.castSucc :=
    fun i j h => hmono (Fin.castSucc_lt_castSucc_iff.2 h)
  obtain ⟨aF, hF⟩ := exists_certificate zeroBound (fun i : Fin n => y i.castSucc)
    hmono'.injective (fun i => hpos _) Z' h0' (by
      have := Finset.card_pos.2 ⟨z, hz⟩
      omega)
  obtain ⟨hFs, hFb⟩ := tailBound n aF (fun i => y i.castSucc) Z' ℓ hmono' (fun i => hpos _)
    (fun i => hhalf _) h0' (by omega) hℓ' hF
  obtain ⟨d₀, h1, h2, h3⟩ := exists_gap_below_max hcard hz hzn
  calc ∑' d, |expSum a y (d + 1)|
      < ∑' d, |expSum aF (fun i => y i.castSucc) (d + 1)| :=
        (tsum_le_lt_of_displaced y hmono hpos hhalf Z hz hzmax h0 hcard a ha aF hF hFs).2
          (summable_tail a y hpos fun i => by linarith [hhalf i]) d₀ h1 h2 h3
    _ ≤ nodeProduct (fun i => y i.castSucc) ℓ := hFb
    _ = nodeProduct y ℓ := nodeProduct_castSucc y hℓn

/-- Theorem 2.2 (equality case). -/
theorem tailEquality : TailEquality := by
  intro c a y Z ℓ hmono hpos hhalf h0 hcard hℓ hℓ1 ha
  cases c with
  | zero =>
    have h1 := ha.1
    rw [expSum, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 zero_ne_one
  | succ n =>
    rw [Nat.add_sub_cancel] at hcard
    constructor
    · intro heq
      by_contra hZ
      exact absurd heq (tsum_lt_nodeProduct a y Z ℓ hmono hpos hhalf h0 hcard hℓ ha hZ).ne
    · rintro rfl
      have h := consecutiveTail (n + 1) a y hmono hpos (fun i => by linarith [hhalf i]) ha
      have e : Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ ℓ) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => by
          have := i.isLt
          have h' : ¬(0 < ℓ + 1 ∧ ℓ + 1 < n + 1) := fun h => hℓ1 (Finset.mem_Ioo.2 h)
          omega
      rw [h.tsum_eq, nodeProduct, e]

end CoefficientMass
