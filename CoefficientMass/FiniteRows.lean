/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarStep

/-!
# Every Row Is a Finite Minimum

This module proves Theorem 6.19(a) of `coefficient-mass-rows.tex`.  Fix minimizers `q_N` of
`μ_r(N, n + |N|)` for `|N| < m` and put `T(N) = t_{m-|N|}(q_N)`.  The sets
`S = {σ_1 < ⋯ < σ_m}` with `σ_{j+1} < T({σ_1, …, σ_j})` form a finite family `𝒮`: removing the
largest element maps a good set of size `j + 1` to a good set of size `j`.  Every `S ∉ 𝒮` has a
first `σ_{j+1} ≥ T(N_j)`, and the far step gives
`1/μ_r(S, n + m) ≥ 1/μ_r(N_j, n + j) ≥ V_r(n + j, j + 1) ≥ V_r(n + m - 1, m)`.

## Definitions

* `goodSets`.

## Theorems

* `filter_lt_max'`.
* `goodSets_succ_subset`.
* `goodSets_finite`.
* `finiteRowsA`.
-/

open Polynomial

namespace CoefficientMass

/-- Sets `N ⊂ ℕ_{>0}` of size `j` with `σ < T({τ ∈ N : τ < σ})` for every `σ ∈ N`. -/
def goodSets (T : Finset ℕ → ℕ) (j : ℕ) : Set (Finset ℕ) :=
  {N | N.card = j ∧ 0 ∉ N ∧ ∀ σ ∈ N, σ < T (N.filter (· < σ))}

theorem filter_lt_max' {N : Finset ℕ} (hne : N.Nonempty) :
    N.filter (· < N.max' hne) = N.erase (N.max' hne) := by
  ext x
  rw [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨hlt.ne, hx⟩
  · rintro ⟨hne', hx⟩
    exact ⟨hx, lt_of_le_of_ne (N.le_max' x hx) hne'⟩

theorem goodSets_succ_subset (T : Finset ℕ → ℕ) (j : ℕ) :
    goodSets T (j + 1) ⊆ ⋃ N ∈ goodSets T j, ⋃ σ ∈ Set.Iio (T N), {insert σ N} := by
  rintro N' ⟨hc, h0, hgood⟩
  have hne : N'.Nonempty := Finset.card_pos.1 (by omega)
  set σ := N'.max' hne
  have hσ : σ ∈ N' := N'.max'_mem hne
  have hfil : ∀ τ ∈ N'.erase σ, (N'.erase σ).filter (· < τ) = N'.filter (· < τ) := by
    intro τ hτ
    have hτσ : τ < σ := lt_of_le_of_ne (N'.le_max' τ (Finset.mem_of_mem_erase hτ))
      (Finset.ne_of_mem_erase hτ)
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hx⟩, hlt⟩
      exact ⟨hx, hlt⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨⟨by omega, hx⟩, hlt⟩
  refine Set.mem_iUnion₂.2 ⟨N'.erase σ, ⟨?_, fun h => h0 (Finset.mem_of_mem_erase h),
    fun τ hτ => ?_⟩, Set.mem_iUnion₂.2 ⟨σ, ?_, ?_⟩⟩
  · rw [Finset.card_erase_of_mem hσ, hc, Nat.add_sub_cancel]
  · rw [hfil τ hτ]
    exact hgood τ (Finset.mem_of_mem_erase hτ)
  · have := hgood σ hσ
    rwa [filter_lt_max' hne] at this
  · rw [Set.mem_singleton_iff, Finset.insert_erase hσ]

theorem goodSets_finite (T : Finset ℕ → ℕ) (j : ℕ) : (goodSets T j).Finite := by
  induction j with
  | zero =>
    refine (Set.finite_singleton ∅).subset fun N hN => ?_
    exact Set.mem_singleton_iff.2 (Finset.card_eq_zero.1 hN.1)
  | succ j ih =>
    exact (ih.biUnion fun N _ => (Set.finite_Iio (T N)).biUnion fun σ _ =>
      Set.finite_singleton _).subset (goodSets_succ_subset T j)

/-- Theorem 6.19(a) of `coefficient-mass-rows.tex`: for `r > 1` and `n, m ≥ 1`, with minimizers
`q_N` of `μ_r(N, n + |N|)` for `|N| < m` and `T(N) = t_{m-|N|}(q_N)`, the family `𝒮` of good
sets of size `m` is finite, and `V_r(n + m, m + 1)` is the minimum of `V_r(n + m - 1, m)` and
`1/μ_r(S, n + m)` over `S ∈ 𝒮`. -/
theorem finiteRowsA {r : ℝ} (hr : 1 < r) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (qN : Finset ℕ → ℝ[X]) (hqN : ∀ N : Finset ℕ, 0 ∉ N → N.card < m →
      (qN N).degree < n + N.card ∧ (qN N).eval 0 = 1 ∧ (∀ s ∈ N, (qN N).eval (s : ℝ) = 0) ∧
        rowPhi r (qN N) = muR r N (n + N.card)) :
    (goodSets (fun N => tM r (qN N) (m - N.card)) m).Finite ∧
      ∀ F : Finset (Finset ℕ),
        (F : Set (Finset ℕ)) = goodSets (fun N => tM r (qN N) (m - N.card)) m →
        rowValue r (n + m) (m + 1) =
          F.fold min (rowValue r (n + m - 1) m) (fun S => 1 / muR r S (n + m)) := by
  refine ⟨goodSets_finite _ m, fun F hF => ?_⟩
  have hdual := (rowValueDual r hr).1 (n + m) (m + 1) (by omega) (by omega)
  have hbdd : BddBelow (Set.range fun S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = m + 1} =>
      1 / muR r S.1 (n + m)) := ⟨0, by
    rintro _ ⟨S, rfl⟩
    exact one_div_nonneg.2 (muR_nonneg hr _ _)⟩
  refine le_antisymm ((Finset.le_fold_min _).2 ⟨?_, fun S hS => ?_⟩) ?_
  · have := (rowMono r hr).1 (n + m) (m + 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this
  · have hS' : S ∈ goodSets (fun N => tM r (qN N) (m - N.card)) m := by
      rw [← hF]
      exact hS
    rw [hdual]
    exact ciInf_le hbdd ⟨S, hS'.2.1, by rw [hS'.1]⟩
  rw [hdual]
  haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = m + 1} :=
    ⟨⟨Finset.Icc 1 m, fun h => by have := (Finset.mem_Icc.1 h).1; omega,
      by rw [Nat.card_Icc]; omega⟩⟩
  refine le_ciInf fun S => ?_
  obtain ⟨S, h0, hc⟩ := S
  have hc' : S.card = m := by omega
  by_cases hg : ∀ σ ∈ S, σ < tM r (qN (S.filter (· < σ))) (m - (S.filter (· < σ)).card)
  · have hSF : S ∈ F := by
      have : S ∈ (F : Set (Finset ℕ)) := by rw [hF]; exact ⟨hc', h0, hg⟩
      exact this
    exact (Finset.fold_min_le _).2 (Or.inr ⟨S, hSF, le_rfl⟩)
  push_neg at hg
  obtain ⟨σ, hσS, hTσ⟩ := hg
  set N := S.filter (· < σ)
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have hσN : σ ∉ N := fun h => (lt_irrefl σ) (Finset.mem_filter.1 h).2
  have hj : N.card < m := hc' ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨hNS, fun h => hσN (h ▸ hσS)⟩)
  have h0N : 0 ∉ N := fun h => h0 (hNS h)
  obtain ⟨hq, hq0, hqN0, hΦ⟩ := hqN N h0N hj
  have hqne : qN N ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  obtain ⟨hT1, hT2⟩ := tM_spec hr (by omega : 1 ≤ m - N.card) hqne
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hσS)
  have hΔ : deltaQ r (qN N) (m - N.card) σ ≤ 0 :=
    (deltaQ_anti hr (by omega) _ (by exact_mod_cast (show 0 < tM r (qN N) (m - N.card) by omega))
      (by exact_mod_cast hTσ)).trans hT2
  have hU : ∀ v ∈ S \ N, (σ : ℝ) ≤ v := fun v hv => by
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.1 hv
    have : ¬ v < σ := fun h => hvN (Finset.mem_filter.2 ⟨hvS, h⟩)
    exact_mod_cast not_lt.1 this
  have hfar := (muR_le_of_far hr hNS hc' hj hq hq0 hqN0 hσ0 hΔ hU).trans_eq hΦ
  have hμS : 0 < muR r S (n + m) := muR_pos hr h0 (by omega)
  have hdiag := rowValue_diag_anti hr hn (by omega : 1 ≤ N.card + 1) (by omega : N.card + 1 ≤ m)
  rw [show n + (N.card + 1) - 1 = n + N.card by omega] at hdiag
  calc F.fold min (rowValue r (n + m - 1) m) (fun S => 1 / muR r S (n + m))
      ≤ rowValue r (n + m - 1) m := (Finset.fold_min_le _).2 (Or.inl le_rfl)
    _ ≤ rowValue r (n + N.card) (N.card + 1) := hdiag
    _ ≤ 1 / muR r N (n + N.card) := rowValue_le_muR hr hn h0N
    _ ≤ 1 / muR r S (n + m) := one_div_le_one_div_of_le hμS hfar

end CoefficientMass
