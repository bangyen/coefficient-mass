/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.AllRowsTwo
import CoefficientMass.RowPrefix

/-!
# Consecutive Prefix Values

This module proves the inequality `ν_{i+1}(n) ≤ a ν_i(n)`, `a = 1/(r - 1)`, stated after
Theorem 5.3 of `coefficient-mass-rows.tex`.  Take `T = [1, i - 1]`, a vertex minimizer `W` of
`μ_{r,D}(T, i - 1 + n)` (Lemma 5.1) and `c = h_{i-1}(W)`.  Then `W ⊇ [1, c - 1]`, so
`Φ_{r,D}^{<c}(r_{ins(W, c)}) = 0`, and `ins(W, c) ⊇ [1, i]`; Lemma 5.2 gives
`μ_{r,D}([1, i], i + n) ≤ a μ_{r,D}([1, i - 1], i - 1 + n)`, and `D → ∞` concludes.

## Definitions

* `PrefixUp`.

## Theorems

* `muRD_le_muR`.
* `muR_le_of_trunc`.
* `muRD_prefix_step`.
* `prefixUp`.
-/

open Polynomial

namespace CoefficientMass

/-- The inequality `ν_{i+1}(n) ≤ ν_i(n)/(r - 1)` for `r > 1` and `i, n ≥ 1`, stated after
Theorem 5.3 of `coefficient-mass-rows.tex`. -/
def PrefixUp : Prop :=
  ∀ r : ℝ, 1 < r → ∀ i n : ℕ, 1 ≤ i → 1 ≤ n → nuR r (i + 1) n ≤ 1 / (r - 1) * nuR r i n

/-- `μ_{r,D}(S, L) ≤ μ_r(S, L)`. -/
theorem muRD_le_muR {r : ℝ} (hr : 1 < r) (D : ℕ) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S)
    (hSL : S.card < L) : muRD r D S L ≤ muR r S L := by
  obtain ⟨hc, hc0, hcS⟩ := confPolyP_admissible h0 hSL
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, hc, hc0, hcS⟩⟩
  refine le_ciInf fun q => ?_
  refine (ciInf_le ⟨0, by
    rintro _ ⟨q', rfl⟩
    exact Finset.sum_nonneg fun _ _ => by positivity⟩ q).trans ?_
  rw [← sum_range_eq_phiD]
  exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_rowPhi hr q.1)

/-- A bound on `μ_{r,D}(S, L)` for all large `D` bounds `μ_r(S, L)`. -/
theorem muR_le_of_trunc {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S)
    (hSL : S.card < L) {B : ℝ} {D₀ : ℕ} (hB : ∀ D, D₀ ≤ D → muRD r D S L ≤ B) :
    muR r S L ≤ B := by
  obtain ⟨hc, hc0, hcS⟩ := confPolyP_admissible h0 hSL
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, hc, hc0, hcS⟩⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨M₀, hM₀⟩ := exists_trunc_ge hr S L hε
  have hμD : muR r S L - ε ≤ muRD r (max M₀ D₀) S L := le_ciInf fun q => by
    obtain ⟨q, hq, hq0, hqS⟩ := q
    have := hM₀ (max M₀ D₀) (le_max_left _ _) q hq hq0 hqS
    rwa [sum_range_eq_phiD] at this
  linarith [hB (max M₀ D₀) (le_max_right _ _)]

/-- The truncated step: `μ_{r,D}([1, i], i + n) ≤ a μ_{r,D}([1, i - 1], i - 1 + n)`. -/
theorem muRD_prefix_step {r : ℝ} (hr : 1 < r) {i n : ℕ} (hi : 1 ≤ i) (hn : 1 ≤ n) (D : ℕ)
    (hD : i - 1 + n + (i - 1) ≤ D) :
    muRD r D (Finset.Icc 1 i) (i + n) ≤
      1 / (r - 1) * muRD r D (Finset.Icc 1 (i - 1)) (i - 1 + n) := by
  set T := Finset.Icc 1 (i - 1)
  have hT0 : 0 ∉ T := fun h => by have := (Finset.mem_Icc.1 h).1; omega
  have hTc : T.card = i - 1 := by rw [Nat.card_Icc]; omega
  have hTs : T.sup id ≤ i - 1 := Finset.sup_le fun x hx => (Finset.mem_Icc.1 hx).2
  obtain ⟨W, hTW, hWD, hWc, hopt⟩ := truncVertex r hr T (i - 1 + n) D hT0 (by omega)
    (by omega)
  have h0W : 0 ∉ W := fun h => by have := (Finset.mem_Icc.1 (hWD h)).1; omega
  obtain ⟨hth, hhW, hgap⟩ := firstGap_spec (i - 1) W
  set c := firstGap (i - 1) W
  -- `W ⊇ [1, c - 1]`
  have hbelow : ∀ x, 1 ≤ x → x < c → x ∈ W := fun x hx1 hxc => by
    rcases le_or_gt x (i - 1) with hxi | hxi
    · exact hTW (Finset.mem_Icc.2 ⟨hx1, hxi⟩)
    · exact hgap x hxi hxc
  have hinsW : ∀ x, 1 ≤ x → x < c → x ∈ ins W c := fun x hx1 hxc =>
    Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hbelow x hx1 hxc, hxc⟩)
  have hopt' : phiD r D (confPolyP W) = muRD r D T (W.card + 1) := by rw [hWc]; exact hopt
  obtain ⟨h1, -⟩ := optIns r hr D T W c h0W hTW (by omega) hhW
    (fun x hx => by have := (Finset.mem_Icc.1 hx).2; omega) hopt'
  have hlt0 : phiLt r D c (confPolyP (ins W c)) = 0 := Finset.sum_eq_zero fun s hs => by
    obtain ⟨hsD, hsc⟩ := Finset.mem_filter.1 hs
    rw [confPolyP_eval_mem (hinsW s (Finset.mem_Icc.1 hsD).1 hsc)
      (by have := (Finset.mem_Icc.1 hsD).1; omega), abs_zero, zero_mul]
  rw [hlt0, mul_zero, add_zero] at h1
  have hr1 : 0 < r - 1 := by linarith
  have hQ : phiD r D (confPolyP (ins W c)) ≤ 1 / (r - 1) * phiD r D (confPolyP W) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hr1]
    linarith
  -- `r_{ins(W, c)}` is admissible for `μ_{r,D}([1, i], i + n)`
  have h0' : 0 ∉ ins W c := fun h => by
    rcases Finset.mem_union.1 h with h | h
    · exact h0W (Finset.mem_filter.1 h).1
    · rcases Finset.mem_insert.1 h with h | h
      · omega
      · obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h
        omega
  obtain ⟨hq, hq0, hqS⟩ := confPolyP_admissible (L := i + n) h0'
    (by rw [card_ins hhW]; omega)
  have hqI : ∀ s ∈ Finset.Icc 1 i, (confPolyP (ins W c)).eval (s : ℝ) = 0 := fun s hs => by
    obtain ⟨hs1, hsIn⟩ := Finset.mem_Icc.1 hs
    refine hqS s ?_
    rcases (show s ≤ c by omega).lt_or_eq with hsc | hsc
    · exact hinsW s hs1 hsc
    · rw [hsc]
      exact mem_ins_self W c
  refine (ciInf_le ⟨0, by
    rintro _ ⟨q', rfl⟩
    exact Finset.sum_nonneg fun _ _ => by positivity⟩
    (⟨_, hq, hq0, hqI⟩ : {q : ℝ[X] // q.degree < ↑(i + n) ∧ q.eval 0 = 1 ∧
      ∀ s ∈ Finset.Icc 1 i, q.eval (s : ℝ) = 0})).trans ?_
  rw [← hWc, ← hopt']
  exact hQ

theorem prefixUp : PrefixUp := by
  intro r hr i n hi hn
  have hI0 : 0 ∉ Finset.Icc 1 i := fun h => by have := (Finset.mem_Icc.1 h).1; omega
  have hT0 : 0 ∉ Finset.Icc 1 (i - 1) := fun h => by have := (Finset.mem_Icc.1 h).1; omega
  have hIc : (Finset.Icc 1 i).card < i + n := by rw [Nat.card_Icc]; omega
  have hTc : (Finset.Icc 1 (i - 1)).card < i - 1 + n := by rw [Nat.card_Icc]; omega
  have ha : 0 ≤ 1 / (r - 1) := one_div_nonneg.2 (by linarith)
  have hstep : muR r (Finset.Icc 1 i) (i + n) ≤
      1 / (r - 1) * muR r (Finset.Icc 1 (i - 1)) (i - 1 + n) :=
    muR_le_of_trunc hr hI0 hIc (D₀ := i - 1 + n + (i - 1)) fun D hD =>
      (muRD_prefix_step hr hi hn D hD).trans
        (mul_le_mul_of_nonneg_left (muRD_le_muR hr D hT0 hTc) ha)
  rw [← muR_prefix hr (by omega : 1 ≤ i + 1) hn, ← muR_prefix hr hi hn,
    Nat.add_sub_cancel, add_comm n i, add_comm n (i - 1)]
  exact hstep

end CoefficientMass
