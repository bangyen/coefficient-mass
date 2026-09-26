/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.IntZeros
import CoefficientMass.RowFarFactor

/-!
# Vertex Minimizers of Truncated Problems

This module proves Lemma 5.1 of `coefficient-mass-rows.tex`.  With
`Φ_{r,D}(q) = ∑_{s = 1}^D |q(s)| r^{-s}` and `μ_{r,D}(S, L)` its infimum over admissible `q`,
every admissible `q` is `r_S p` with `deg p ≤ L - 1 - |S|` and `p(0) = 1`, and
`Φ_{r,D}(q) = ∑_{s ∈ N} ω(s) |p(s)|` with `N = [1, D] \ S` and `ω = |r_S| r^{-s} > 0` on `N`.
The vertex step replaces `p` by some `r_Y`, `Y ⊆ N`, `|Y| = L - 1 - |S|`; the best of these
finitely many `Y` attains `μ_{r,D}(S, L)` with `W = S ∪ Y`.

## Definitions

* `phiD`.
* `muRD`.
* `TruncVertex`.

## Theorems

* `phiD_eq_nodeSum`.
* `truncVertex`.
-/

open Polynomial

namespace CoefficientMass

/-- `Φ_{r,D}(q) = ∑_{s = 1}^D |q(s)| r^{-s}`. -/
noncomputable def phiD (r : ℝ) (D : ℕ) (q : ℝ[X]) : ℝ :=
  ∑ s ∈ Finset.Icc 1 D, |q.eval (s : ℝ)| * (1 / r) ^ s

/-- `μ_{r,D}(S, L)`: the infimum of `Φ_{r,D}(q)` over real `q` with `deg q < L`, `q(0) = 1` and
`q|_S = 0`. -/
noncomputable def muRD (r : ℝ) (D : ℕ) (S : Finset ℕ) (L : ℕ) : ℝ :=
  ⨅ q : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0}, phiD r D q.1

/-- Lemma 5.1 of `coefficient-mass-rows.tex`: for `r > 1`, finite `S ⊂ ℕ_{>0}`, `L > |S|`
and `D ≥ L + max(S ∪ {0})`, some `W` with `S ⊆ W ⊆ [1, D]` and `|W| = L - 1` has
`Φ_{r,D}(r_W) = μ_{r,D}(S, L)`. -/
def TruncVertex : Prop :=
  ∀ (r : ℝ), 1 < r → ∀ (S : Finset ℕ) (L D : ℕ), 0 ∉ S → S.card < L → L + S.sup id ≤ D →
    ∃ W : Finset ℕ, S ⊆ W ∧ W ⊆ Finset.Icc 1 D ∧ W.card + 1 = L ∧
      phiD r D (confPolyP W) = muRD r D S L

/-- `Φ_{r,D}(r_S p) = ∑_{s ∈ [1, D] \ S} |r_S(s)| r^{-s} |p(s)|`. -/
theorem phiD_eq_nodeSum (r : ℝ) (D : ℕ) {S : Finset ℕ} (hSD : S ⊆ Finset.Icc 1 D)
    {q p : ℝ[X]} (hfac : ∀ y : ℝ, q.eval y = (confPolyP S).eval y * p.eval y) :
    phiD r D q = nodeSum (fun s => |confPoly S s| * (1 / r) ^ s) (Finset.Icc 1 D \ S) p := by
  classical
  rw [phiD, nodeSum, ← Finset.sum_sdiff hSD]
  have hS : ∑ s ∈ S, |q.eval (s : ℝ)| * (1 / r) ^ s = 0 := Finset.sum_eq_zero fun s hs => by
    rw [hfac, confPolyP_eval_mem hs (by have := (Finset.mem_Icc.1 (hSD hs)).1; omega), zero_mul,
      abs_zero, zero_mul]
  rw [hS, add_zero]
  exact Finset.sum_congr rfl fun s _ => by simp only [hfac, abs_mul, confPoly_eq_eval]; ring

theorem truncVertex : TruncVertex := by
  classical
  intro r hr S L D h0 hSL hD
  have hx : 0 < 1 / r := by positivity
  have hSD : S ⊆ Finset.Icc 1 D := fun s hs => Finset.mem_Icc.2
    ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ hs), (Finset.le_sup (f := id) hs).trans (by omega)⟩
  set N := Finset.Icc 1 D \ S
  set ω : ℕ → ℝ := fun s => |confPoly S s| * (1 / r) ^ s
  set d := L - 1 - S.card
  have hNc : N.card = D - S.card := by
    rw [Finset.card_sdiff_of_subset hSD, Nat.card_Icc, Nat.add_sub_cancel]
  have hω : ∀ s ∈ N, 0 < ω s := fun s hs => by
    obtain ⟨hsD, hsS⟩ := Finset.mem_sdiff.1 hs
    refine mul_pos (abs_pos.2 ?_) (by positivity)
    rw [confPoly]
    refine Finset.prod_ne_zero_iff.2 fun σ hσ h => hsS ?_
    have hσ0 : (σ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 fun h' => h0 (h' ▸ hσ)
    rw [sub_eq_zero, eq_div_iff hσ0, one_mul, Nat.cast_inj] at h
    rwa [← h]
  have hN0 : 0 ∉ N := fun h => by have := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 h).1).1; omega
  -- the best vertex
  obtain ⟨Y, hY, hYmin⟩ := (N.powersetCard d).exists_min_image
    (fun Y => nodeSum ω N (confPolyP Y)) (Finset.powersetCard_nonempty.2 (by omega))
  obtain ⟨hYN, hYc⟩ := Finset.mem_powersetCard.1 hY
  have hdisj : Disjoint S Y := Finset.disjoint_left.2 fun s hs hsY =>
    (Finset.mem_sdiff.1 (hYN hsY)).2 hs
  set W := S ∪ Y
  have hW0 : 0 ∉ W := fun h => by
    rcases Finset.mem_union.1 h with h | h
    · exact h0 h
    · exact hN0 (hYN h)
  have hWc : W.card + 1 = L := by rw [Finset.card_union_of_disjoint hdisj, hYc]; omega
  have hWfac : ∀ y : ℝ, (confPolyP W).eval y = (confPolyP S).eval y * (confPolyP Y).eval y :=
    fun y => by rw [eval_confPolyP, eval_confPolyP, eval_confPolyP, Finset.prod_union hdisj]
  have hadm := confPolyP_admissible hW0 (show W.card < L by omega)
  refine ⟨W, Finset.subset_union_left, Finset.union_subset hSD fun y hy =>
    (Finset.mem_sdiff.1 (hYN hy)).1, hWc, le_antisymm ?_ ?_⟩
  · -- `r_W` beats every admissible `q`
    haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧
        ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
      ⟨⟨_, hadm.1, hadm.2.1, fun s hs => hadm.2.2 s (Finset.mem_union_left _ hs)⟩⟩
    refine le_ciInf fun q => ?_
    obtain ⟨q, hq, hq0, hqS⟩ := q
    change _ ≤ phiD r D q
    obtain ⟨p, hpdeg, hp0, hfac⟩ := factor_conf h0 hq hq0 hqS
    obtain ⟨Y', hY'N, hY'c, hY'⟩ := exists_int_zeros (ω := ω) hω hN0 (n := d + 1) (by omega)
      (by omega) _ p (by omega) hp0 le_rfl
    rw [phiD_eq_nodeSum r D hSD hWfac, phiD_eq_nodeSum r D hSD hfac]
    exact (hYmin Y' (Finset.mem_powersetCard.2 ⟨hY'N, by omega⟩)).trans hY'
  · exact ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact Finset.sum_nonneg fun _ _ => by positivity⟩
      (⟨confPolyP W, hadm.1, hadm.2.1, fun s hs => hadm.2.2 s (Finset.mem_union_left _ hs)⟩ :
        {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})

end CoefficientMass
