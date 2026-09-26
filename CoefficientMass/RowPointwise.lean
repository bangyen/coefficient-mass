/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDefs
import Mathlib.Data.Nat.Choose.Basic

/-!
# A Uniform Bound on the Exempted Factor

This module proves Lemma 3.2 of `coefficient-mass-rows.tex`.  If `σ_1 < ⋯ < σ_j` are the
elements of `S` below `s`, then `σ_l ≥ l` and `|1 - s/σ_l| ≤ (s - l)/l`, while the elements
at least `s` contribute factors in `[0, 1]`; so `|r_S(s)| ≤ binom(s - 1, j)`.  With
`|S| ≤ k - 1` unimodality bounds this by `W_k(s) = binom(s - 1, min(k - 1, ⌊(s - 1)/2⌋))`,
which is `binom(s - 1, k - 1)` for `s ≥ 2k - 1`.

## Definitions

* `wK`.
* `RowPointwise`.

## Theorems

* `choose_le_choose_of_le_half`.
* `prod_below_le`.
* `abs_confPoly_le_choose`.
* `choose_le_wK`.
* `wK_eq`.
* `rowPointwise`.
-/

namespace CoefficientMass

/-- `W_k(s) = binom(s - 1, min(k - 1, ⌊(s - 1)/2⌋))`. -/
def wK (k s : ℕ) : ℕ :=
  (s - 1).choose (min (k - 1) ((s - 1) / 2))

/-- Lemma 3.2 of `coefficient-mass-rows.tex`: for finite `S ⊂ ℕ_{>0}` and `s ≥ 1`,
`|r_S(s)| ≤ binom(s - 1, j_s)` with `j_s = |S ∩ [1, s - 1]|`; if `|S| ≤ k - 1` then
`|r_S(s)| ≤ W_k(s)`; and `W_k(s) = binom(s - 1, k - 1)` for `s ≥ 2k - 1`. -/
def RowPointwise : Prop :=
  (∀ (S : Finset ℕ), 0 ∉ S → ∀ s : ℕ, 1 ≤ s →
    |confPoly S s| ≤ ((s - 1).choose (S.filter (· < s)).card : ℝ) ∧
      ∀ k : ℕ, S.card + 1 ≤ k → |confPoly S s| ≤ (wK k s : ℝ)) ∧
  ∀ k s : ℕ, 2 * k - 1 ≤ s → wK k s = (s - 1).choose (k - 1)

/-- The binomial coefficients increase up to the middle. -/
theorem choose_le_choose_of_le_half (n j : ℕ) :
    ∀ d, j + d ≤ n / 2 → n.choose j ≤ n.choose (j + d) := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `∏_{σ ∈ T} (s - σ)/σ ≤ binom(s - 1, |T|)` for `T ⊆ [1, s - 1]`. -/
theorem prod_below_le (s : ℕ) (T : Finset ℕ) :
    (∀ σ ∈ T, 1 ≤ σ ∧ σ < s) →
      ∏ σ ∈ T, (((s : ℝ) - σ) / σ) ≤ ((s - 1).choose T.card : ℝ) := by
  classical
  induction T using Finset.induction_on_max with
  | h0 => intro _; rw [Finset.prod_empty, Finset.card_empty, Nat.choose_zero_right, Nat.cast_one]
  | step a T hlt ih =>
    intro h
    have haT : a ∉ T := fun h' => lt_irrefl a (hlt a h')
    obtain ⟨ha1, has⟩ := h a (Finset.mem_insert_self a T)
    have hT := ih fun σ hσ => h σ (Finset.mem_insert_of_mem hσ)
    set j := T.card
    have hja : j + 1 ≤ a := by
      have := Finset.card_le_card (show T ⊆ Finset.Icc 1 (a - 1) from fun σ hσ => by
        have := hlt σ hσ
        have := (h σ (Finset.mem_insert_of_mem hσ)).1
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [Nat.card_Icc] at this
      omega
    rw [Finset.prod_insert haT, Finset.card_insert_of_notMem haT]
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hj0 : (0 : ℝ) < j + 1 := by positivity
    have hfac : ((s : ℝ) - a) / a ≤ ((s : ℝ) - (j + 1)) / (j + 1) := by
      rw [div_le_div_iff₀ ha0 hj0]
      have : ((j : ℝ) + 1) ≤ a := by exact_mod_cast hja
      nlinarith
    have hfac0 : 0 ≤ ((s : ℝ) - a) / a := by
      have : (a : ℝ) ≤ s := by exact_mod_cast has.le
      exact div_nonneg (by linarith) ha0.le
    have hchoose : ((s - 1).choose (j + 1) : ℝ) =
        ((s - 1).choose j : ℝ) * (((s : ℝ) - (j + 1)) / (j + 1)) := by
      have h := Nat.choose_succ_right_eq (s - 1) j
      have hsj : ((s - 1 - j : ℕ) : ℝ) = (s : ℝ) - (j + 1) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      have h' : ((s - 1).choose (j + 1) : ℝ) * (j + 1) =
          ((s - 1).choose j : ℝ) * (s - (j + 1)) := by
        rw [← hsj]
        exact_mod_cast h
      field_simp
      linarith
    rw [hchoose, mul_comm]
    exact mul_le_mul hT hfac hfac0 (Nat.cast_nonneg _)

/-- `|r_S(s)| ≤ binom(s - 1, j_s)`. -/
theorem abs_confPoly_le_choose {S : Finset ℕ} (h0 : 0 ∉ S) {s : ℕ} (hs : 1 ≤ s) :
    |confPoly S s| ≤ ((s - 1).choose (S.filter (· < s)).card : ℝ) := by
  classical
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [confPoly, Finset.abs_prod, ← Finset.prod_filter_mul_prod_filter_not S (· < s)]
  have hbelow : ∏ σ ∈ S.filter (· < s), |1 - (s : ℝ) / σ| =
      ∏ σ ∈ S.filter (· < s), (((s : ℝ) - σ) / σ) := Finset.prod_congr rfl fun σ hσ => by
    obtain ⟨hσS, hσs⟩ := Finset.mem_filter.1 hσ
    have hσ0 : (0 : ℝ) < σ := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hσS)
    have hσs' : (σ : ℝ) < s := by exact_mod_cast hσs
    rw [abs_of_neg (by rw [sub_neg, lt_div_iff₀ hσ0]; linarith), neg_sub, div_sub_one hσ0.ne']
  have habove : ∏ σ ∈ S.filter (fun σ => ¬ σ < s), |1 - (s : ℝ) / σ| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun σ hσ => by
      obtain ⟨hσS, hσs⟩ := Finset.mem_filter.1 hσ
      have hσ0 : (0 : ℝ) < σ := by exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ hσS)
      have hσs' : (s : ℝ) ≤ σ := by exact_mod_cast not_lt.1 hσs
      have h1 : (s : ℝ) / σ ≤ 1 := by rw [div_le_one hσ0]; exact hσs'
      have h2 : 0 ≤ (s : ℝ) / σ := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hbelow]
  have hprod := prod_below_le s (S.filter (· < s)) fun σ hσ => by
    obtain ⟨hσS, hσs⟩ := Finset.mem_filter.1 hσ
    exact ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ hσS), hσs⟩
  have hnn : 0 ≤ ∏ σ ∈ S.filter (· < s), (((s : ℝ) - σ) / σ) :=
    Finset.prod_nonneg fun σ hσ => by
      obtain ⟨_, hσs⟩ := Finset.mem_filter.1 hσ
      have : (σ : ℝ) ≤ s := by exact_mod_cast hσs.le
      exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  calc _ ≤ (∏ σ ∈ S.filter (· < s), (((s : ℝ) - σ) / σ)) * 1 :=
        mul_le_mul_of_nonneg_left habove hnn
    _ ≤ _ := by rw [mul_one]; exact hprod

/-- `binom(s - 1, j) ≤ W_k(s)` for `j ≤ k - 1`. -/
theorem choose_le_wK {k s j : ℕ} (hjk : j ≤ k - 1) : (s - 1).choose j ≤ wK k s := by
  rw [wK]
  rcases le_or_gt j ((s - 1) / 2) with h | h
  · have := choose_le_choose_of_le_half (s - 1) j (min (k - 1) ((s - 1) / 2) - j) (by omega)
    rwa [show j + (min (k - 1) ((s - 1) / 2) - j) = min (k - 1) ((s - 1) / 2) by omega] at this
  · rw [min_eq_right (by omega)]
    exact Nat.choose_le_middle j (s - 1)

theorem wK_eq {k s : ℕ} (h : 2 * k - 1 ≤ s) : wK k s = (s - 1).choose (k - 1) := by
  rw [wK, min_eq_left (by omega)]

theorem rowPointwise : RowPointwise := by
  refine ⟨fun S h0 s hs => ⟨abs_confPoly_le_choose h0 hs, fun k hk => ?_⟩,
    fun k s h => wK_eq h⟩
  refine (abs_confPoly_le_choose h0 hs).trans ?_
  exact_mod_cast choose_le_wK ((Finset.card_filter_le S _).trans (by omega))

end CoefficientMass
