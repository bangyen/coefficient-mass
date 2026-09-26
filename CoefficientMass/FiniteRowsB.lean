/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FiniteRows

/-!
# A Finite Tree Bounds a Row

This module proves Theorem 6.19(b) of `coefficient-mass-rows.tex`.  For `x ∈ S` let
`P_x = {y ∈ S : y < x}`.  While every earlier `y` has `y < T_{P_y}`, the tree hypothesis keeps
`P_x = P_y ∪ {y}` (`y = max P_x`) in `𝒯`.  At the least `x ∈ S` with `x ≥ T_{P_x}` the far step
gives `μ_r(S, n + m) ≤ Φ_r(q_{P_x}) ≤ B`; if there is none, the leaf hypothesis at
`x = max S` gives it.

## Theorems

* `filter_lt_eq_insert`.
* `prefix_mem_tree`.
* `finiteRowsB`.
-/

open Polynomial

namespace CoefficientMass

/-- `{w ∈ S : w < x} = {w ∈ S : w < y} ∪ {y}` for `y = max {w ∈ S : w < x}`. -/
theorem filter_lt_eq_insert {S : Finset ℕ} {x : ℕ} (hne : (S.filter (· < x)).Nonempty) :
    S.filter (· < x) = insert ((S.filter (· < x)).max' hne)
      (S.filter (· < (S.filter (· < x)).max' hne)) := by
  set y := (S.filter (· < x)).max' hne
  have hy := Finset.mem_filter.1 ((S.filter (· < x)).max'_mem hne)
  ext w
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hlt⟩
    have : w ≤ y := (S.filter (· < x)).le_max' w (Finset.mem_filter.2 ⟨hw, hlt⟩)
    rcases lt_or_eq_of_le this with h | h
    · exact Or.inr ⟨hw, h⟩
    · exact Or.inl h
  · rintro (rfl | ⟨hw, hlt⟩)
    · exact hy
    · exact ⟨hw, hlt.trans hy.2⟩

/-- If no `y ∈ S` below `x` has escaped (`y < T_{P_y}`), then `P_x ∈ 𝒯`. -/
theorem prefix_mem_tree {m : ℕ} (𝒯 : Set (Finset ℕ)) (hT0 : ∅ ∈ 𝒯) (TN : Finset ℕ → ℕ)
    (hstep : ∀ N ∈ 𝒯, N.card + 2 ≤ m → ∀ σ : ℕ, N.sup id < σ → σ < TN N → insert σ N ∈ 𝒯)
    {S : Finset ℕ} (h0 : 0 ∉ S) (hc : S.card = m) :
    ∀ x ∈ S, (∀ y ∈ S, y < x → y < TN (S.filter (· < y))) → S.filter (· < x) ∈ 𝒯 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx hbefore
    rcases (S.filter (· < x)).eq_empty_or_nonempty with he | hne
    · rw [he]
      exact hT0
    obtain ⟨y, hyeq⟩ : ∃ y, y = (S.filter (· < x)).max' hne := ⟨_, rfl⟩
    have hy : y ∈ S ∧ y < x := by
      rw [hyeq]
      exact Finset.mem_filter.1 ((S.filter (· < x)).max'_mem hne)
    have hPx : S.filter (· < x) = insert y (S.filter (· < y)) := by
      rw [hyeq]
      exact filter_lt_eq_insert hne
    have hPy := ih y hy.2 hy.1 fun z hz hzy => hbefore z hz (hzy.trans hy.2)
    rw [hPx]
    refine hstep _ hPy ?_ y ?_ (hbefore y hy.1 hy.2)
    · have h1 : (S.filter (· < x)).card + 1 ≤ m := by
        rw [← hc]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _,
          fun h => ?_⟩)
        rw [← h] at hx
        exact lt_irrefl x (Finset.mem_filter.1 hx).2
      have h2 := Finset.card_insert_of_notMem (s := S.filter (· < y)) (a := y)
        (fun h => lt_irrefl y (Finset.mem_filter.1 h).2)
      rw [← hPx] at h2
      omega
    · rcases (S.filter (· < y)).eq_empty_or_nonempty with h | h
      · rw [h, Finset.sup_empty]
        exact Nat.pos_of_ne_zero fun h' => h0 (h' ▸ hy.1)
      · obtain ⟨w, hw, hws⟩ := Finset.exists_mem_eq_sup _ h id
        rw [hws]
        exact (Finset.mem_filter.1 hw).2

/-- Theorem 6.19(b) of `coefficient-mass-rows.tex`: let `B` be real and let `𝒯 ∋ ∅` be a family of
finite sets of size `< m`, with `q_N` admissible for `μ_r(N, n + |N|)`, `Φ_r(q_N) ≤ B`, and
integers `T_N ≥ 1` with `Δ_{q_N, m-|N|}(T_N) ≤ 0`.  If `N ∪ {σ} ∈ 𝒯` whenever `N ∈ 𝒯`,
`|N| ≤ m - 2` and `max N < σ < T_N`, and `μ_r(N ∪ {σ}, n + m) ≤ B` whenever `N ∈ 𝒯`,
`|N| = m - 1` and `max N < σ < T_N`, then `μ_r(S, n + m) ≤ B` for every `S ⊂ ℕ_{>0}` with
`|S| = m`, and `V_r(n + m, m + 1) ≥ 1/B`. -/
theorem finiteRowsB {r : ℝ} (hr : 1 < r) {n m : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (𝒯 : Set (Finset ℕ)) (hT0 : ∅ ∈ 𝒯) (hTc : ∀ N ∈ 𝒯, N.card < m)
    (qN : Finset ℕ → ℝ[X]) (TN : Finset ℕ → ℕ)
    (hq : ∀ N ∈ 𝒯, (qN N).degree < n + N.card ∧ (qN N).eval 0 = 1 ∧
      (∀ s ∈ N, (qN N).eval (s : ℝ) = 0) ∧ rowPhi r (qN N) ≤ B ∧ 1 ≤ TN N ∧
        deltaQ r (qN N) (m - N.card) (TN N) ≤ 0)
    (hstep : ∀ N ∈ 𝒯, N.card + 2 ≤ m → ∀ σ : ℕ, N.sup id < σ → σ < TN N → insert σ N ∈ 𝒯)
    (hleaf : ∀ N ∈ 𝒯, N.card + 1 = m → ∀ σ : ℕ, N.sup id < σ → σ < TN N →
      muR r (insert σ N) (n + m) ≤ B) :
    (∀ S : Finset ℕ, 0 ∉ S → S.card = m → muR r S (n + m) ≤ B) ∧
      1 / B ≤ rowValue r (n + m) (m + 1) := by
  have hm : 1 ≤ m := by have := hTc ∅ hT0; rw [Finset.card_empty] at this; omega
  have hsup : ∀ {S : Finset ℕ} {x : ℕ}, 0 ∉ S → x ∈ S → (S.filter (· < x)).sup id < x :=
    fun {S x} h0 hx => by
      rcases (S.filter (· < x)).eq_empty_or_nonempty with h | h
      · rw [h, Finset.sup_empty]
        exact Nat.pos_of_ne_zero fun h' => h0 (h' ▸ hx)
      · obtain ⟨w, hw, hws⟩ := Finset.exists_mem_eq_sup _ h id
        rw [hws]
        exact (Finset.mem_filter.1 hw).2
  have hall : ∀ S : Finset ℕ, 0 ∉ S → S.card = m → muR r S (n + m) ≤ B := by
    intro S h0 hc
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hpre := prefix_mem_tree 𝒯 hT0 TN hstep h0 hc
    by_cases hbad : ∀ x ∈ S, x < TN (S.filter (· < x))
    · -- no escape: the leaf at `z = max S`
      set z := S.max' hSne
      have hz := S.max'_mem hSne
      have hPz := hpre z hz fun y hy _ => hbad y hy
      have hSz : S = insert z (S.filter (· < z)) := by
        ext w
        rw [Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hw
          rcases lt_or_eq_of_le (S.le_max' w hw) with h | h
          · exact Or.inr ⟨hw, h⟩
          · exact Or.inl h
        · rintro (rfl | ⟨hw, -⟩)
          · exact hz
          · exact hw
      have hcard : (S.filter (· < z)).card + 1 = m := by
        have := Finset.card_insert_of_notMem (s := S.filter (· < z)) (a := z)
          (fun h => lt_irrefl z (Finset.mem_filter.1 h).2)
        rw [← hSz, hc] at this
        omega
      have := hleaf _ hPz hcard z (hsup h0 hz) (hbad z hz)
      rwa [← hSz] at this
    · -- the first escape
      push_neg at hbad
      have hne : (S.filter fun x => TN (S.filter (· < x)) ≤ x).Nonempty := by
        obtain ⟨x, hx, hxT⟩ := hbad
        exact ⟨x, Finset.mem_filter.2 ⟨hx, hxT⟩⟩
      set x := (S.filter fun x => TN (S.filter (· < x)) ≤ x).min' hne
      obtain ⟨hx, hxT⟩ := Finset.mem_filter.1
        ((S.filter fun x => TN (S.filter (· < x)) ≤ x).min'_mem hne)
      have hbefore : ∀ y ∈ S, y < x → y < TN (S.filter (· < y)) := fun y hy hyx => by
        by_contra h
        push_neg at h
        exact absurd ((S.filter fun x => TN (S.filter (· < x)) ≤ x).min'_le y
          (Finset.mem_filter.2 ⟨hy, h⟩)) (not_le.2 hyx)
      have hN := hpre x hx hbefore
      obtain ⟨hdeg, hq0, hqN, hΦ, hT1, hΔ⟩ := hq _ hN
      have hx0 : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hx)
      have hTx : (TN (S.filter (· < x)) : ℝ) ≤ x := by exact_mod_cast hxT
      have hΔx := (deltaQ_anti hr (by have := hTc _ hN; omega) _
        (by exact_mod_cast (show 0 < TN (S.filter (· < x)) by omega)) hTx).trans hΔ
      refine (muR_le_of_far hr (Finset.filter_subset _ _) hc (hTc _ hN) hdeg hq0 hqN hx0 hΔx
        fun v hv => ?_).trans hΦ
      obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.1 hv
      have : ¬ v < x := fun h => hvN (Finset.mem_filter.2 ⟨hvS, h⟩)
      exact_mod_cast not_lt.1 this
  refine ⟨hall, ?_⟩
  rw [(rowValueDual r hr).1 (n + m) (m + 1) (by omega) (by omega)]
  haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = m + 1} :=
    ⟨⟨Finset.Icc 1 m, fun h => by have := (Finset.mem_Icc.1 h).1; omega,
      by rw [Nat.card_Icc]; omega⟩⟩
  refine le_ciInf fun S => ?_
  exact one_div_le_one_div_of_le (muR_pos hr S.2.1 (by omega)) (hall S.1 S.2.1 (by omega))

end CoefficientMass
