/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.VertexStep
import CoefficientMass.MuRMin
import CoefficientMass.RowLast

/-!
# Certifying a Vertex

This module states and proves Lemma 6.11 of `coefficient-mass-rows.tex`.  The certificate
test is `rowPhi_le_of_cert`, `cert_of_rowPhi_le` and `rowPhi_lt_of_cert`.  For the existence
claim, start from a minimizer (`exists_muR_min`) and apply `vGood_step` until
`deg q = |Z|`, so `q = r_Z`; then `|Z| = L - 1`, since otherwise a far zero
`(1 - s/σ) r_Z` would do better (`rowPhi_mul_lin`).

## Definitions

* `VertexOpt`.

## Theorems

* `vGood_vertex`.
* `exists_vertex`.
* `vertexOpt`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 6.11 of `coefficient-mass-rows.tex`. -/
def VertexOpt : Prop :=
  (∀ r : ℝ, 1 < r → ∀ S Z : Finset ℕ, S ⊆ Z → 0 ∉ Z →
    (rowPhi r (confPolyP Z) = muR r S (Z.card + 1) ↔
      ∀ y ∈ Z \ S, |gY r Z y| ≤ |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y) ∧
    ((∀ y ∈ Z \ S, |gY r Z y| < |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y) →
      ∀ q : ℝ[X], q.degree < ↑(Z.card + 1) → q.eval 0 = 1 → (∀ s ∈ S, q.eval (s : ℝ) = 0) →
        q ≠ confPolyP Z → rowPhi r (confPolyP Z) < rowPhi r q)) ∧
  ∀ r : ℝ, 1 < r → ∀ S : Finset ℕ, 0 ∉ S → ∀ L : ℕ, S.card < L →
    ∃ Z : Finset ℕ, S ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 = L ∧ rowPhi r (confPolyP Z) = muR r S L

theorem vGood_vertex {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (n : ℕ) :
    ∀ (Z : Finset ℕ) (m : ℕ) (q : ℝ[X]), VGood r S L Z m q → m - Z.card = n →
      ∃ Z' : Finset ℕ, S ⊆ Z' ∧ 0 ∉ Z' ∧ Z'.card < L ∧
        rowPhi r (confPolyP Z') = muR r S L := by
  refine Nat.strong_induction_on n fun n ih => ?_
  intro Z m q hg hn
  by_cases hZm : Z.card < m
  · obtain ⟨Z', m', q', hg', hlt⟩ := vGood_step hr hg hZm
    exact ih _ (by omega) Z' m' q' hg' rfl
  unfold VGood at hg
  obtain ⟨hSZ, h0, hZc, hmL, hqn, hq0, hqZ, hqμ⟩ := hg
  have hq : q.degree < ↑(Z.card + 1) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (by omega))
  rw [eq_confPolyP_of_card h0 rfl hq hq0 hqZ] at hqμ
  exact ⟨Z, hSZ, h0, by omega, hqμ⟩

theorem exists_vertex {r : ℝ} (hr : 1 < r) {S : Finset ℕ} (h0 : 0 ∉ S) {L : ℕ}
    (hSL : S.card < L) : ∃ Z : Finset ℕ, S ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 = L ∧
      rowPhi r (confPolyP Z) = muR r S L := by
  obtain ⟨q, hq, hq0, hqS, hqμ⟩ := exists_muR_min hr h0 hSL
  have hqne : q ≠ 0 := fun h => by
    rw [h, eval_zero] at hq0
    exact zero_ne_one hq0
  have hqn : q.natDegree < L := by
    rw [degree_eq_natDegree hqne] at hq
    exact_mod_cast hq
  have hg : VGood r S L S (L - 1) q := by
    unfold VGood
    exact ⟨subset_rfl, h0, by omega, by omega, by omega, hq0, hqS, hqμ⟩
  obtain ⟨Z, hSZ, hZ0, hZL, hZμ⟩ := vGood_vertex hr _ S (L - 1) q hg rfl
  refine ⟨Z, hSZ, hZ0, ?_, hZμ⟩
  by_contra hne
  -- a far zero `(1 - s/σ) r_Z` does better
  obtain ⟨-, hp0, hpZ⟩ := confPolyP_admissible (L := Z.card + 1) hZ0 (by omega)
  have hpne : confPolyP Z ≠ 0 := fun h => by
    rw [h, eval_zero] at hp0
    exact zero_ne_one hp0
  obtain ⟨N, hN⟩ := exists_remR_lt hr (confPolyP Z) (half_pos (psiR_pos hr hpne))
  have hσ : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hR := remR_anti hr (confPolyP Z) (Nat.cast_nonneg N)
    (show (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by push_cast; linarith)
  have hΦ := rowPhi_mul_lin hr (confPolyP Z) hσ
  have hlin : (1 - C (1 / ((N + 1 : ℕ) : ℝ)) * X).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; omega)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have hdeg : (confPolyP Z * (1 - C (1 / ((N + 1 : ℕ) : ℝ)) * X)).natDegree < L :=
    natDegree_mul_le.trans_lt (by have := natDegree_confPolyP Z; omega)
  have hle := muR_le_adm (r := r) (S := S) (degree_le_natDegree.trans_lt
    (by exact_mod_cast hdeg)) (by rw [eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X,
      mul_zero, sub_zero, mul_one, hp0])
    (fun s hs => by rw [eval_mul, hpZ s (hSZ hs), zero_mul])
  have : 0 < (psiR r (confPolyP Z) - 2 * remR r (confPolyP Z) ((N + 1 : ℕ) : ℝ)) /
      ((N + 1 : ℕ) : ℝ) := div_pos (by linarith) hσ
  linarith

theorem vertexOpt : VertexOpt := by
  unfold VertexOpt
  refine ⟨fun r hr S Z hSZ h0 => ⟨⟨fun h => ?_, fun h => ?_⟩, fun h q hq hq0 hqS hne =>
    rowPhi_lt_of_cert hr hSZ h0 h hq hq0 hqS hne⟩, fun r hr S h0 L hSL => exists_vertex hr h0 hSL⟩
  · exact cert_of_rowPhi_le hr hSZ h0 fun q hq hq0 hqS => h.le.trans (muR_le_adm hq hq0 hqS)
  · have hS0 : 0 ∉ S := fun h' => h0 (hSZ h')
    obtain ⟨q, hq, hq0, hqS, hqμ⟩ :=
      exists_muR_min hr hS0 (Nat.lt_succ_of_le (Finset.card_le_card hSZ))
    obtain ⟨hZd, hZ0, hZZ⟩ := confPolyP_admissible (L := Z.card + 1) h0 (by omega)
    exact le_antisymm ((rowPhi_le_of_cert hr hSZ h0 h hq hq0 hqS).trans hqμ.le)
      (muR_le_adm hZd hZ0 fun s hs => hZZ s (hSZ hs))

end CoefficientMass
