/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ConfPrefix
import CoefficientMass.RowFar

/-!
# The Last Row

This module proves Corollary 2.4 of `coefficient-mass-rows.tex`: `V_r(L, L) = r - 1` for
`r ≥ 2` and `V_r(L, L) = (r - 1)^L` for `1 < r ≤ 2`.  With `|S| = L - 1` the admissible
polynomial of `μ_r(S, L)` is forced to be `r_S`, so `μ_r(S, L) = Φ_r(S)`, which Lemma 2.3
bounds by `a` for `r ≥ 2` and by `a^L` for `r ≤ 2`, `a = 1/(r - 1)`.  The upper bounds are
Proposition 2.1(c) with `n = 1`, where `μ_r(∅, 1) = Φ_r(∅) = a`, and Proposition 2.1(b) with
`S = [1, L - 1]`, where `Φ_r(S) = a^L`.

## Definitions

* `LastRow`.

## Theorems

* `muR_le_conf`.
* `eq_confPolyP_of_card`.
* `muR_last`.
* `lastRow`.
-/

open Polynomial

namespace CoefficientMass

/-- Corollary 2.4 of `coefficient-mass-rows.tex`: `V_r(L, L) = r - 1` for `r ≥ 2` and
`V_r(L, L) = (r - 1)^L` for `1 < r ≤ 2`. -/
def LastRow : Prop :=
  ∀ r : ℝ, 1 < r → ∀ L : ℕ, 1 ≤ L →
    (2 ≤ r → rowValue r L L = r - 1) ∧ (r ≤ 2 → rowValue r L L = (r - 1) ^ L)

theorem muR_le_conf {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S)
    (hS : S.card < L) : muR r S L ≤ rowPhi r (confPolyP S) :=
  ciInf_le ⟨0, by
    rintro _ ⟨q, rfl⟩
    exact tsum_nonneg fun _ => by
      have : 0 < 1 / r := by positivity
      positivity⟩
    (⟨confPolyP S, confPolyP_admissible h0 hS⟩ :
      {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})

/-- With `|S| = L - 1` the admissible polynomial is `r_S`. -/
theorem eq_confPolyP_of_card {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S) (hSc : S.card + 1 = L)
    {q : ℝ[X]} (hq : q.degree < L) (hq0 : q.eval 0 = 1)
    (hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0) : q = confPolyP S := by
  classical
  obtain ⟨hc, hc0, hcS⟩ := confPolyP_admissible h0 (show S.card < L by omega)
  set T : Finset ℝ := insert 0 (S.image fun s : ℕ => (s : ℝ))
  have h0T : (0 : ℝ) ∉ S.image fun s : ℕ => (s : ℝ) := fun h => by
    obtain ⟨s, hs, hs0⟩ := Finset.mem_image.1 h
    exact h0 (Nat.cast_eq_zero.1 hs0 ▸ hs)
  have hT : T.card = L := by
    rw [Finset.card_insert_of_notMem h0T, Finset.card_image_of_injective _ Nat.cast_injective, hSc]
  have hdeg : ∀ p : ℝ[X], p.degree < L → p.natDegree < L := fun p hp => by
    rcases eq_or_ne p 0 with h | h
    · rw [h, natDegree_zero]
      omega
    · rw [degree_eq_natDegree h] at hp
      exact_mod_cast hp
  have hd := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (q - confPolyP S) T
    (fun i hi => by
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [eval_sub, hq0, hc0, sub_self]
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hi
        rw [eval_sub, hqS s hs, hcS s hs, sub_self])
    (by
      rw [hT]
      exact (natDegree_sub_le _ _).trans_lt (max_lt (hdeg q hq) (hdeg _ hc)))
  exact sub_eq_zero.1 hd

/-- `μ_r(S, L) = Φ_r(S)` when `|S| = L - 1`. -/
theorem muR_last {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S)
    (hSc : S.card + 1 = L) : muR r S L = rowPhi r (confPolyP S) := by
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, confPolyP_admissible h0 (by omega)⟩⟩
  refine le_antisymm (muR_le_conf hr h0 (by omega)) (le_ciInf fun q => ?_)
  rw [eq_confPolyP_of_card h0 hSc q.2.1 q.2.2.1 q.2.2.2]

theorem lastRow : LastRow := by
  intro r hr L hL
  have ha : 0 < 1 / (r - 1) := by
    have : 0 < r - 1 := by linarith
    positivity
  have hdual := (rowValueDual r hr).1 L L hL le_rfl
  haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = L} :=
    ⟨⟨Finset.Icc 1 (L - 1), fun h => by
      have := (Finset.mem_Icc.1 h).1
      omega, by rw [Nat.card_Icc]; omega⟩⟩
  -- every `1/μ_r(S, L)` is at least `1/c` once `Φ_r(S) ≤ c`
  have hlow : ∀ c : ℝ, (∀ S : Finset ℕ, 0 ∉ S → S.card + 1 = L → rowPhi r (confPolyP S) ≤ c) →
      1 / c ≤ rowValue r L L := fun c hc => by
    rw [hdual]
    refine le_ciInf fun S => ?_
    rw [muR_last hr S.2.1 S.2.2]
    have hpos : 0 < rowPhi r (confPolyP S.1) := by
      have := muR_pos hr S.2.1 (show S.1.card < L by have := S.2.2; omega)
      rwa [muR_last hr S.2.1 S.2.2] at this
    exact one_div_le_one_div_of_le hpos (hc S.1 S.2.1 S.2.2)
  have hempty : rowPhi r (confPolyP ∅) = 1 / (r - 1) := by
    rw [← Finset.Icc_eq_empty (show ¬ 1 ≤ 0 by norm_num), rowPhi_prefix hr, zero_add, pow_one]
  refine ⟨fun hr2 => le_antisymm ?_ ?_, fun hr2 => le_antisymm ?_ ?_⟩
  · -- the top row of `(x - r)^1`
    have h := rowValueTop r hr L L hL le_rfl
    rw [Nat.sub_self, zero_add, (rowValueDual r hr).2 1 le_rfl,
      muR_last hr (Finset.notMem_empty 0) (by rw [Finset.card_empty]), hempty,
      one_div_one_div] at h
    exact h
  · have := hlow (1 / (r - 1)) fun S h0 _ => by
      have h := rowPhi_le_filter hr2 0 _ S rfl h0
      rwa [Finset.filter_false_of_mem fun s hs hs0 => h0 (Nat.le_zero.1 hs0 ▸ hs), hempty] at h
    rwa [one_div_one_div] at this
  · -- the prefix `S = [1, L - 1]`
    have h := rowValue_le_inv hr (k := L) hL le_rfl (S := Finset.Icc 1 (L - 1))
      (fun h => by have := (Finset.mem_Icc.1 h).1; omega) (by rw [Nat.card_Icc]; omega)
    rw [muR_last hr (S := Finset.Icc 1 (L - 1)) (L := L)
      (fun h => by have := (Finset.mem_Icc.1 h).1; omega) (by rw [Nat.card_Icc]; omega),
      rowPhi_prefix hr, Nat.sub_add_cancel hL, one_div_pow, one_div_one_div] at h
    exact h
  · have := hlow ((1 / (r - 1)) ^ L) fun S h0 hSc => by
      have h := rowPhi_le_pow hr hr2 _ S rfl h0
      rwa [hSc] at h
    rwa [one_div_pow, one_div_one_div] at this

end CoefficientMass
