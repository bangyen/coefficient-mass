/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ConfDel
import Mathlib.Data.Nat.Nth

/-!
# Filling Holes

This module builds the sets of Propositions 4.9 and 4.12 of `coefficient-mass.tex`.
The holes of a finite `A ⊂ ℕ_{>0}` are the positive integers outside `A`, listed
increasingly as `c_1 < c_2 < ⋯`.  Keeping the first `r` holes `K`, filling the next
`n - 1` and putting `N = c_{r + n - 1}`, `Y = {1, …, N} \ K` and `Z = Y ∪ A` gives
`Z ⊇ A`, `|Z| ≤ |A| + n - 1` and `Φ(Z) ≤ Φ(Y)`: the elements of `Z` above `N` are
deleted one at a time, largest first, by Lemma 4.6.

## Definitions

* `hole`.

## Theorems

* `infinite_holes`.
* `hole_mem`.
* `hole_strictMono`.
* `hole_add_le`.
* `exists_hole_eq`.
* `confTail_le_of_above`.
* `fill_holes`.
-/

namespace CoefficientMass

/-- The hole `c_{i+1}` of `A`: the `i`-th positive integer outside `A`, from `0`. -/
noncomputable def hole (A : Finset ℕ) (i : ℕ) : ℕ :=
  Nat.nth (fun x => 0 < x ∧ x ∉ A) i

theorem infinite_holes (A : Finset ℕ) : (setOf fun x => 0 < x ∧ x ∉ A).Infinite := by
  obtain ⟨n, hn⟩ := A.exists_nat_subset_range
  refine Set.infinite_of_not_bddAbove fun ⟨M, hM⟩ => ?_
  have h1 : M + n + 1 ∈ setOf fun x => 0 < x ∧ x ∉ A :=
    ⟨by omega, fun h => by have := Finset.mem_range.1 (hn h); omega⟩
  have := hM h1
  omega

theorem hole_mem (A : Finset ℕ) (i : ℕ) : 0 < hole A i ∧ hole A i ∉ A :=
  Nat.nth_mem_of_infinite (infinite_holes A) i

theorem hole_strictMono (A : Finset ℕ) : StrictMono (hole A) :=
  Nat.nth_strictMono (infinite_holes A)

theorem hole_add_le (A : Finset ℕ) (i k : ℕ) : hole A i + k ≤ hole A (i + k) := by
  induction k with
  | zero => simp only [Nat.add_zero, le_refl]
  | succ k ih =>
    have := hole_strictMono A (show i + k < i + (k + 1) by omega)
    omega

/-- Every hole up to `c_{j+1}` is some `c_{i+1}` with `i ≤ j`. -/
theorem exists_hole_eq {A : Finset ℕ} {x j : ℕ} (hx : 0 < x) (hxA : x ∉ A)
    (hj : x ≤ hole A j) : ∃ i ≤ j, hole A i = x := by
  refine ⟨Nat.count (fun x => 0 < x ∧ x ∉ A) x, ?_, Nat.nth_count ⟨hx, hxA⟩⟩
  have := Nat.count_monotone (fun x => 0 < x ∧ x ∉ A) hj
  rwa [hole, Nat.count_nth_of_infinite (infinite_holes A)] at this

/-- Adding elements above every element of `Y` does not increase `Φ`. -/
theorem confTail_le_of_above : ∀ (n : ℕ) (Z Y : Finset ℕ), (Z \ Y).card = n → Y ⊆ Z →
    0 ∉ Z → (∀ x ∈ Z \ Y, ∀ y ∈ Y, y < x) → confTail Z ≤ confTail Y := by
  intro n
  induction n with
  | zero =>
    intro Z Y hc hYZ _ _
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hc
    rw [Finset.Subset.antisymm hc hYZ]
  | succ n ih =>
    intro Z Y hc hYZ h0 habove
    obtain ⟨x, hx⟩ : (Z \ Y).Nonempty := Finset.card_pos.1 (by omega)
    have hne : Z.Nonempty := ⟨x, (Finset.mem_sdiff.1 hx).1⟩
    set z := Z.max' hne
    have hzZ : z ∈ Z := Z.max'_mem hne
    have hzY : z ∉ Y := fun h => by
      have := habove x hx z h
      have := Z.le_max' x (Finset.mem_sdiff.1 hx).1
      omega
    have hz : z ∈ Z \ Y := Finset.mem_sdiff.2 ⟨hzZ, hzY⟩
    refine (confTail_erase_max hne h0).1.trans (ih _ Y ?_ ?_ ?_ ?_)
    · rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hz, hc, Nat.add_sub_cancel]
    · exact fun y hy => Finset.mem_erase.2 ⟨fun h => hzY (by subst h; exact hy), hYZ hy⟩
    · exact fun h => h0 (Finset.mem_of_mem_erase h)
    · intro x hx
      rw [Finset.erase_sdiff_comm] at hx
      exact habove x (Finset.mem_of_mem_erase hx)

/-- Keep the first `r` holes and fill the next `n - 1`. -/
theorem fill_holes {A : Finset ℕ} (h0 : 0 ∉ A) {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) {K : Finset ℕ}
    (hK : K = (Finset.range r).image (hole A)) {N : ℕ} (hN : N = hole A (r + n - 2)) :
    A ⊆ (Finset.Icc 1 N \ K) ∪ A ∧ 0 ∉ (Finset.Icc 1 N \ K) ∪ A ∧
      ((Finset.Icc 1 N \ K) ∪ A).card + 1 ≤ A.card + n ∧
      confTail ((Finset.Icc 1 N \ K) ∪ A) ≤ confTail (Finset.Icc 1 N \ K) := by
  set Y := Finset.Icc 1 N \ K
  have hY0 : 0 ∉ Y := fun h => by
    have := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 h).1).1
    omega
  have hZ0 : 0 ∉ Y ∪ A := fun h => (Finset.mem_union.1 h).elim hY0 h0
  -- the elements of `Y` outside `A` are the filled holes
  have hfill : Y \ A ⊆ (Finset.Ico r (r + n - 1)).image (hole A) := fun x hx => by
    obtain ⟨hxY, hxA⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨hxI, hxK⟩ := Finset.mem_sdiff.1 hxY
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hxI
    obtain ⟨i, hi, rfl⟩ := exists_hole_eq (by omega) hxA (hN ▸ h2)
    refine Finset.mem_image.2 ⟨i, Finset.mem_Ico.2 ⟨?_, by omega⟩, rfl⟩
    by_contra hir
    exact hxK (hK ▸ Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  refine ⟨Finset.subset_union_right, hZ0, ?_, ?_⟩
  · have hcard := (Finset.card_le_card hfill).trans Finset.card_image_le
    rw [Nat.card_Ico] at hcard
    have := Finset.card_sdiff_add_card Y A
    omega
  · refine confTail_le_of_above _ _ Y rfl Finset.subset_union_left hZ0 fun x hx y hy => ?_
    obtain ⟨hxZ, hxY⟩ := Finset.mem_sdiff.1 hx
    have hxA : x ∈ A := (Finset.mem_union.1 hxZ).resolve_left hxY
    have hyN := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hy).1).2
    by_contra hle
    push_neg at hle
    have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hxA)
    have hxK : x ∈ K := by
      by_contra hxK
      exact hxY (Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hx1, by omega⟩, hxK⟩)
    rw [hK] at hxK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hxK
    exact (hole_mem A i).2 hxA

end CoefficientMass
