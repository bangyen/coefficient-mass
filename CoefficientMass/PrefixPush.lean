/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.CrossRows
import CoefficientMass.RowPrefix

/-!
# Pushing Exempted Positions into the Prefix

This module proves Lemma 6.1 of `coefficient-mass-rows.tex`.  With
`A_i(p) = ∑_s binom(s - 1, i - 1) r^{-s} |p(s)| = Φ_r(r_{[1, i - 1]} p)`, every finite
`S ⊂ ℕ_{>0}` has `Φ_r(r_S p) ≤ max_{i ≤ |S| + 1} A_i(p)`.  If `S` is not an initial block, its
first gap `g` lies below `σ = max S`, and Lemma 4.1(b) with `y = g` bounds `Φ_r(r_S p)` by the
values at `S \ {σ}` (one element fewer) and at `(S \ {σ}) ∪ {g}` (the same size, a smaller
sum); induction on the size and then on the sum concludes.

## Definitions

* `prefA`.

## Theorems

* `confPolyP_insert_mul`.
* `eq_Icc_of_gap`.
* `prefixPush_aux`.
* `prefixPush`.
-/

open Polynomial

namespace CoefficientMass

/-- `A_i(p) = ∑_s binom(s - 1, i - 1) r^{-s} |p(s)|`. -/
noncomputable def prefA (r : ℝ) (i : ℕ) (p : ℝ[X]) : ℝ :=
  ∑' s : ℕ, prefixWeight r i s * |p.eval (s : ℝ)|

/-- `r_{Z ∪ {z}} p = r_Z p (1 - s/z)`. -/
theorem confPolyP_insert_mul {Z : Finset ℕ} {z : ℕ} (hz : z ∉ Z) (p : ℝ[X]) :
    confPolyP (insert z Z) * p = confPolyP Z * p * (1 - C (1 / (z : ℝ)) * X) := by
  simp only [confPolyP, Finset.prod_insert hz, C_neg, C_1]
  ring

/-- If every element of `S ⊂ ℕ_{>0}` lies below its first gap, `S` is an initial block. -/
theorem eq_Icc_of_gap {S : Finset ℕ} (h0 : 0 ∉ S) (hS : ∀ x ∈ S, x < firstGap 0 S) :
    S = Finset.Icc 1 S.card := by
  obtain ⟨-, -, hgap⟩ := firstGap_spec 0 S
  have hS' : S = Finset.Icc 1 (firstGap 0 S - 1) := by
    ext x
    rw [Finset.mem_Icc]
    constructor
    · intro hx
      have := hS x hx
      exact ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ hx), by omega⟩
    · intro hx
      exact hgap x (by omega) (by omega)
  conv_rhs => rw [hS', Nat.card_Icc, Nat.add_sub_cancel]
  exact hS'

theorem prefixPush_aux {r : ℝ} (hr : 1 < r) (p : ℝ[X]) (n : ℕ) :
    ∀ m : ℕ, ∀ S : Finset ℕ, S.card = n → S.sum id = m → 0 ∉ S →
      ∃ i, 1 ≤ i ∧ i ≤ n + 1 ∧ rowPhi r (confPolyP S * p) ≤ prefA r i p := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro S hSn hSm h0
      by_cases hS : S = Finset.Icc 1 S.card
      · refine ⟨S.card + 1, by omega, by omega, le_of_eq (rowPhi_prefix_mul r (i := S.card + 1) fun y => ?_)⟩
        rw [eval_mul, Nat.add_sub_cancel, ← hS]
      obtain ⟨hg0, hgS, -⟩ := firstGap_spec 0 S
      set g := firstGap 0 S
      have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h => hS (by
        rw [h, Finset.card_empty, Finset.Icc_eq_empty (by norm_num)])
      set σ := S.max' hne
      have hσS : σ ∈ S := S.max'_mem hne
      have hgσ : g < σ := by
        by_contra hle
        exact hS (eq_Icc_of_gap h0 fun x hx => lt_of_le_of_ne ((S.le_max' x hx).trans
          (not_lt.1 hle)) fun h => hgS (h ▸ hx))
      have hσU : σ ∉ S.erase σ := Finset.notMem_erase σ S
      have hgU : g ∉ S.erase σ := fun h => hgS (Finset.mem_of_mem_erase h)
      have h0U : 0 ∉ S.erase σ := fun h => h0 (Finset.mem_of_mem_erase h)
      have hUc : (S.erase σ).card + 1 = n := by
        rw [Finset.card_erase_of_mem hσS]
        have := Finset.card_pos.2 hne
        omega
      have hcross := (crossing r hr).2 (confPolyP (S.erase σ) * p) g σ (by exact_mod_cast hg0)
        (by exact_mod_cast hgσ.le)
      rw [← confPolyP_insert_mul hσU, Finset.insert_erase hσS,
        ← confPolyP_insert_mul hgU] at hcross
      obtain ⟨i, hi1, hin, hi⟩ := ihn (S.erase σ).card (by omega) _ (S.erase σ) rfl rfl h0U
      have hsum : (insert g (S.erase σ)).sum id < m := by
        rw [Finset.sum_insert hgU, ← hSm, ← Finset.add_sum_erase S id hσS]
        exact Nat.add_lt_add_right hgσ _
      obtain ⟨j, hj1, hjn, hj⟩ := ihm _ hsum (insert g (S.erase σ))
        (by rw [Finset.card_insert_of_notMem hgU]; omega) rfl
        (fun h => by
          rcases Finset.mem_insert.1 h with h | h
          · omega
          · exact h0U h)
      rcases le_total (rowPhi r (confPolyP (S.erase σ) * p))
        (rowPhi r (confPolyP (insert g (S.erase σ)) * p)) with h | h
      · exact ⟨j, hj1, hjn, hcross.trans ((max_eq_right h).le.trans hj)⟩
      · exact ⟨i, hi1, by omega, hcross.trans ((max_eq_left h).le.trans hi)⟩

/-- Lemma 6.1 of `coefficient-mass-rows.tex`: for `r > 1`, real `p` and finite
`S ⊂ ℕ_{>0}`, `Φ_r(r_S p) ≤ A_i(p)` for some `1 ≤ i ≤ |S| + 1`. -/
theorem prefixPush {r : ℝ} (hr : 1 < r) (p : ℝ[X]) {S : Finset ℕ} (h0 : 0 ∉ S) :
    ∃ i, 1 ≤ i ∧ i ≤ S.card + 1 ∧ rowPhi r (confPolyP S * p) ≤ prefA r i p :=
  prefixPush_aux hr p S.card _ S rfl rfl h0

end CoefficientMass
