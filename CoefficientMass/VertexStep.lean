/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.VertexLine
import Mathlib.Analysis.Polynomial.Basic

/-!
# One Step Toward a Vertex Minimizer

This module proves the induction step for the existence claim of Lemma 6.11 of
`coefficient-mass-rows.tex`.  Let `q` be a minimizer of `μ_r(S, L)` with `deg q ≤ m`
vanishing on `Z ⊇ S`, `|Z| < m`, and no zero at a positive integer outside `Z`.  With
`d = ±s r_Z(s)` chosen so the slope `∑_s sgn(q(s)) d(s) r^{-s}` is `≤ 0`, `Φ_r(q + t d)` stays
at `μ_r(S, L)` while `t ≥ 0` keeps the signs of `q`.  The largest such `t` exists, and there
`q + t d` gains a new integer zero or loses degree: otherwise `d = O(q + t d)` lets `t` grow.

## Definitions

* `VGood`.

## Theorems

* `vGood_insert`.
* `vGood_step`.
-/

open Polynomial Filter Topology Asymptotics

namespace CoefficientMass

/-- `q` minimizes `μ_r(S, L)`, `deg q ≤ m < L`, and `q` vanishes on `Z ⊇ S` with
`0 ∉ Z` and `|Z| ≤ m`. -/
def VGood (r : ℝ) (S : Finset ℕ) (L : ℕ) (Z : Finset ℕ) (m : ℕ) (q : ℝ[X]) : Prop :=
  S ⊆ Z ∧ 0 ∉ Z ∧ Z.card ≤ m ∧ m < L ∧ q.natDegree ≤ m ∧ q.eval 0 = 1 ∧
    (∀ z ∈ Z, q.eval (z : ℝ) = 0) ∧ rowPhi r q = muR r S L

/-- A new integer zero `k + 1 ∉ Z` lowers `m - |Z|`. -/
theorem vGood_insert {r : ℝ} {S : Finset ℕ} {L : ℕ} {Z : Finset ℕ} {m : ℕ} {q : ℝ[X]}
    (hg : VGood r S L Z m q) (hZm : Z.card < m) {k : ℕ} (hkZ : k + 1 ∉ Z)
    (hk : q.eval ((k + 1 : ℕ) : ℝ) = 0) :
    VGood r S L (insert (k + 1) Z) m q ∧ m - (insert (k + 1) Z).card < m - Z.card := by
  unfold VGood at hg ⊢
  obtain ⟨hSZ, h0, -, hmL, hqn, hq0, hqZ, hqμ⟩ := hg
  rw [Finset.card_insert_of_notMem hkZ]
  refine ⟨⟨hSZ.trans (Finset.subset_insert _ _), fun h => ?_, by omega, hmL, hqn, hq0,
    fun z hz => ?_, hqμ⟩, by omega⟩
  · rcases Finset.mem_insert.1 h with h | h
    · omega
    · exact h0 h
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hk
    · exact hqZ z hz

theorem vGood_step {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} {Z : Finset ℕ} {m : ℕ}
    {q : ℝ[X]} (hg : VGood r S L Z m q) (hZm : Z.card < m) :
    ∃ (Z' : Finset ℕ) (m' : ℕ) (q' : ℝ[X]), VGood r S L Z' m' q' ∧
      m' - Z'.card < m - Z.card := by
  by_cases hnew : ∃ k : ℕ, k + 1 ∉ Z ∧ q.eval ((k + 1 : ℕ) : ℝ) = 0
  · obtain ⟨k, hkZ, hk⟩ := hnew
    exact ⟨_, _, _, vGood_insert hg hZm hkZ hk⟩
  push_neg at hnew
  unfold VGood at hg
  obtain ⟨hSZ, h0, hZc, hmL, hqn, hq0, hqZ, hqμ⟩ := hg
  obtain ⟨-, hp0, hpZ⟩ := confPolyP_admissible (L := Z.card + 1) h0 (by omega)
  -- the direction `d = ±s r_Z(s)` with nonpositive slope
  have hd₀Z : ∀ z ∈ Z, (X * confPolyP Z).eval (z : ℝ) = 0 := fun z hz => by
    rw [eval_mul, hpZ z hz, mul_zero]
  have hd₀0 : (X * confPolyP Z).eval 0 = 0 := by rw [eval_mul, eval_X, zero_mul]
  have hd₀n : (X * confPolyP Z).natDegree ≤ m :=
    natDegree_mul_le.trans (by
      have := natDegree_confPolyP Z
      have := natDegree_X_le (R := ℝ)
      omega)
  have hd₀ne : X * confPolyP Z ≠ 0 := mul_ne_zero X_ne_zero fun h => by
    rw [h, eval_zero] at hp0
    exact zero_ne_one hp0
  obtain ⟨d, hdZ, hd0, hdn, hdne, hℓ⟩ : ∃ d : ℝ[X], (∀ z ∈ Z, d.eval (z : ℝ) = 0) ∧
      d.eval 0 = 0 ∧ d.natDegree ≤ m ∧ d ≠ 0 ∧ ∑' k : ℕ, Real.sign (q.eval ((k + 1 : ℕ) : ℝ)) *
        d.eval ((k + 1 : ℕ) : ℝ) * (1 / r) ^ (k + 1) ≤ 0 := by
    by_cases h : ∑' k : ℕ, Real.sign (q.eval ((k + 1 : ℕ) : ℝ)) *
        (X * confPolyP Z).eval ((k + 1 : ℕ) : ℝ) * (1 / r) ^ (k + 1) ≤ 0
    · exact ⟨_, hd₀Z, hd₀0, hd₀n, hd₀ne, h⟩
    · refine ⟨-(X * confPolyP Z), fun z hz => by rw [eval_neg, hd₀Z z hz, neg_zero],
        by rw [eval_neg, hd₀0, neg_zero], by rw [natDegree_neg]; exact hd₀n, neg_ne_zero.2 hd₀ne,
        ?_⟩
      simp only [eval_neg, mul_neg, neg_mul, tsum_neg]
      linarith
  have hqd : ∀ k : ℕ, q.eval ((k + 1 : ℕ) : ℝ) = 0 → d.eval ((k + 1 : ℕ) : ℝ) = 0 :=
    fun k hk => hdZ _ (by by_contra h; exact hnew k h hk)
  have hadm : ∀ t : ℝ, (q + C t * d).natDegree ≤ m ∧ (q + C t * d).eval 0 = 1 ∧
      ∀ z ∈ Z, (q + C t * d).eval (z : ℝ) = 0 := fun t =>
    ⟨(natDegree_add_le _ _).trans (max_le hqn ((natDegree_C_mul_le _ _).trans hdn)),
      by rw [eval_add, eval_mul, eval_C, hq0, hd0, mul_zero, add_zero],
      fun z hz => by rw [eval_add, eval_mul, eval_C, hqZ z hz, hdZ z hz, mul_zero, add_zero]⟩
  have hμle : ∀ t : ℝ, muR r S L ≤ rowPhi r (q + C t * d) := fun t => by
    obtain ⟨hn, h0', hZ'⟩ := hadm t
    exact muR_le_adm hr (degree_le_natDegree.trans_lt (by exact_mod_cast hn.trans_lt hmL)) h0'
      fun s hs => hZ' s (hSZ hs)
  -- the sign-preserving set `T`
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ, T = Set.Ici 0 ∩ ⋂ k : ℕ, {t : ℝ | 0 ≤
      q.eval ((k + 1 : ℕ) : ℝ) * (q.eval ((k + 1 : ℕ) : ℝ) + t * d.eval ((k + 1 : ℕ) : ℝ))} :=
    ⟨_, rfl⟩
  have hmem : ∀ t : ℝ, t ∈ T ↔ 0 ≤ t ∧ ∀ k : ℕ, 0 ≤ q.eval ((k + 1 : ℕ) : ℝ) *
      (q.eval ((k + 1 : ℕ) : ℝ) + t * d.eval ((k + 1 : ℕ) : ℝ)) := fun t => by
    rw [hTdef]
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter, Set.mem_setOf_eq]
  have hTμ : ∀ t ∈ T, rowPhi r (q + C t * d) = muR r S L := fun t ht => by
    obtain ⟨ht0, htk⟩ := (hmem t).1 ht
    refine le_antisymm ?_ (hμle t)
    rw [rowPhi_add_line hr hqd htk, hqμ]
    nlinarith
  have hdpos := rowPhi_pos hr hdne
  have hbdd : BddAbove T := ⟨2 * muR r S L / rowPhi r d, fun t ht => by
    rw [le_div_iff₀ hdpos]
    have h := mul_rowPhi_le hr q d ((hmem t).1 ht).1
    rw [hTμ t ht, hqμ] at h
    linarith⟩
  have hTc : IsClosed T := by
    rw [hTdef]
    exact isClosed_Ici.inter (isClosed_iInter fun k => isClosed_le continuous_const
      (by fun_prop))
  have hT0 : (0 : ℝ) ∈ T := (hmem 0).2 ⟨le_rfl, fun k => by
    rw [zero_mul, add_zero]
    exact mul_self_nonneg _⟩
  have hts := hTc.csSup_mem ⟨0, hT0⟩ hbdd
  obtain ⟨hun, hu0, huZ⟩ := hadm (sSup T)
  have hgu : VGood r S L Z m (q + C (sSup T) * d) := by
    unfold VGood
    exact ⟨hSZ, h0, hZc, hmL, hun, hu0, huZ, hTμ _ hts⟩
  -- a new zero, or a lower degree
  by_cases hA : ∃ k : ℕ, k + 1 ∉ Z ∧ (q + C (sSup T) * d).eval ((k + 1 : ℕ) : ℝ) = 0
  · obtain ⟨k, hkZ, hk⟩ := hA
    exact ⟨_, _, _, vGood_insert hgu hZm hkZ hk⟩
  by_cases hB : (q + C (sSup T) * d).natDegree < m
  · refine ⟨Z, m - 1, q + C (sSup T) * d, ?_, by omega⟩
    unfold VGood
    exact ⟨hSZ, h0, by omega, by omega, by omega, hu0, huZ, hTμ _ hts⟩
  exfalso
  push_neg at hA hB
  obtain ⟨u, hu_def⟩ : ∃ u, u = q + C (sSup T) * d := ⟨_, rfl⟩
  rw [← hu_def] at hA hB hu0
  have hune : u ≠ 0 := fun h => by
    rw [h, eval_zero] at hu0
    exact zero_ne_one hu0
  have hdeg : d.degree ≤ u.degree := by
    rw [degree_eq_natDegree hune]
    exact degree_le_natDegree.trans (by exact_mod_cast hdn.trans hB)
  obtain ⟨c, hc, hcO⟩ := (isBigO_atTop_of_degree_le d u hdeg).exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcO.bound
  -- a small `ε > 0` keeping the signs of `u`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε * c < 1 ∧ ∀ k ∈ Finset.range (⌈N⌉₊ + 1),
      k + 1 ∈ Z ∨ ε * |d.eval ((k + 1 : ℕ) : ℝ)| < |u.eval ((k + 1 : ℕ) : ℝ)| := by
    have hc1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * c < 1 :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / c))
        fun ε hε => (lt_div_iff₀ hc).1 hε.2
    refine eventually_mem_nhdsWithin.and (hc1.and ((Filter.eventually_all_finset _).2
      fun k _ => ?_))
    by_cases hk : k + 1 ∈ Z
    · exact Eventually.of_forall fun _ => Or.inl hk
    have hpos : 0 < |u.eval ((k + 1 : ℕ) : ℝ)| / (|d.eval ((k + 1 : ℕ) : ℝ)| + 1) :=
      div_pos (abs_pos.2 (hA k hk)) (by positivity)
    have hIoo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ε ∈ Set.Ioo 0 (|u.eval ((k + 1 : ℕ) : ℝ)| / (|d.eval ((k + 1 : ℕ) : ℝ)| + 1)) :=
      Ioo_mem_nhdsGT hpos
    refine hIoo.mono fun ε hε => Or.inr ?_
    have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |d.eval ((k + 1 : ℕ) : ℝ)| + 1)).1 hε.2
    nlinarith [hε.1, abs_nonneg (d.eval ((k + 1 : ℕ) : ℝ))]
  obtain ⟨ε, hε0, hεc, hεF⟩ := hev.exists
  have hQ : ∀ k : ℕ, k + 1 ∈ Z ∨ ε * |d.eval ((k + 1 : ℕ) : ℝ)| < |u.eval ((k + 1 : ℕ) : ℝ)| :=
    fun k => by
    by_cases hk : k + 1 ∈ Z
    · exact Or.inl hk
    by_cases hkF : k ∈ Finset.range (⌈N⌉₊ + 1)
    · exact hεF k hkF
    right
    have hkN : N ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.mem_range, not_lt] at hkF
      have h1 := Nat.le_ceil N
      have h2 : ((⌈N⌉₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hkF
      push_cast
      linarith
    have h := hN _ hkN
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hu := abs_pos.2 (hA k hk)
    calc ε * |d.eval ((k + 1 : ℕ) : ℝ)| ≤ ε * (c * |u.eval ((k + 1 : ℕ) : ℝ)|) :=
          mul_le_mul_of_nonneg_left h hε0.le
      _ = ε * c * |u.eval ((k + 1 : ℕ) : ℝ)| := by ring
      _ < 1 * |u.eval ((k + 1 : ℕ) : ℝ)| := mul_lt_mul_of_pos_right hεc hu
      _ = |u.eval ((k + 1 : ℕ) : ℝ)| := one_mul _
  have hkε : ∀ k : ℕ, 0 ≤ q.eval ((k + 1 : ℕ) : ℝ) *
      (q.eval ((k + 1 : ℕ) : ℝ) + (sSup T + ε) * d.eval ((k + 1 : ℕ) : ℝ)) := fun k => by
    rcases hQ k with hk | hk
    · simp only [hqZ _ hk, zero_mul, le_refl]
    have hab := ((hmem _).1 hts).2 k
    have he : |ε * d.eval ((k + 1 : ℕ) : ℝ)| < |u.eval ((k + 1 : ℕ) : ℝ)| := by
      rwa [abs_mul, abs_of_pos hε0]
    rw [hu_def, eval_add, eval_mul, eval_C] at he
    have := sign_step hab he
    linarith [show q.eval ((k + 1 : ℕ) : ℝ) * (q.eval ((k + 1 : ℕ) : ℝ) +
      sSup T * d.eval ((k + 1 : ℕ) : ℝ) + ε * d.eval ((k + 1 : ℕ) : ℝ)) =
        q.eval ((k + 1 : ℕ) : ℝ) * (q.eval ((k + 1 : ℕ) : ℝ) +
          (sSup T + ε) * d.eval ((k + 1 : ℕ) : ℝ)) by ring]
  have hmε : sSup T + ε ∈ T := (hmem _).2 ⟨by linarith [((hmem _).1 hts).1], hkε⟩
  linarith [le_csSup hbdd hmε]

end CoefficientMass
