/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.MuRMin
import CoefficientMass.SecondRowId

/-!
# The Second Row Is a Finite Minimum

This module proves Theorem 6.12 of `coefficient-mass-rows.tex`.  With
`η_σ(n) = μ_r({σ}, n + 1)`, the polynomial `(1 - s/σ) p` is admissible for `η_σ(n)`, which gives
(a).  A minimizer `p_*` of `ν_1(n)` exists, and the least `σ_* ≥ 1` with
`2R_{p_*}(σ_*) ≤ Ψ_r(p_*)` makes every far position cost at most `ν_1(n)`; so
`V_r(n + 1, 2) = min(1/ν_1(n), min_{1 ≤ σ < σ_*} 1/η_σ(n))`, and since `η_1(n) = ν_2(n)` the
prefix identity fails at `(r, n + 1, 2)` exactly when some `2 ≤ σ < σ_*` has
`η_σ(n) > max(ν_1(n), ν_2(n))`.

## Definitions

* `SecondRow`.

## Theorems

* `muR_empty_eq`.
* `muR_one_eq`.
* `etaR_le`.
* `secondRow`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 6.12 of `coefficient-mass-rows.tex`: for `r > 1` and `n ≥ 1`, (a)
`η_σ(n) ≤ Φ_r(p) - (Ψ_r(p) - 2R_p(σ))/σ` for `p ∈ Q_n`; (b) some `p_* ∈ Q_n` has
`Φ_r(p_*) = ν_1(n)`, and for each such `p_*` and the least `σ_* ≥ 1` with
`2R_{p_*}(σ_*) ≤ Ψ_r(p_*)`, `η_σ(n) ≤ ν_1(n)` for `σ ≥ σ_*` (strictly for `σ > σ_*`) and
`V_r(n + 1, 2) = min(1/ν_1(n), min_{1 ≤ σ < σ_*} 1/η_σ(n))`; (c) the prefix identity fails at
`(r, n + 1, 2)` if and only if `η_σ(n) > max(ν_1(n), ν_2(n))` for some `2 ≤ σ < σ_*`. -/
def SecondRow : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n : ℕ, 1 ≤ n →
    (∀ p : ℝ[X], p.degree < n → p.eval 0 = 1 → ∀ σ : ℕ, 1 ≤ σ →
      muR r {σ} (n + 1) ≤ rowPhi r p - (psiR r p - 2 * remR r p σ) / σ) ∧
    (∃ p : ℝ[X], p.degree < n ∧ p.eval 0 = 1 ∧ rowPhi r p = nuR r 1 n) ∧
    ∀ p : ℝ[X], p.degree < n → p.eval 0 = 1 → rowPhi r p = nuR r 1 n →
      ∃ σs : ℕ, 1 ≤ σs ∧ 2 * remR r p σs ≤ psiR r p ∧
        (∀ σ : ℕ, 1 ≤ σ → σ < σs → psiR r p < 2 * remR r p σ) ∧
        (∀ σ : ℕ, σs ≤ σ → muR r {σ} (n + 1) ≤ nuR r 1 n) ∧
        (∀ σ : ℕ, σs < σ → muR r {σ} (n + 1) < nuR r 1 n) ∧
        rowValue r (n + 1) 2 =
          (Finset.Ico 1 σs).fold min (1 / nuR r 1 n) (fun σ => 1 / muR r {σ} (n + 1)) ∧
        (rowValue r (n + 1) 2 ≠ min (1 / nuR r 1 n) (1 / nuR r 2 n) ↔
          ∃ σ : ℕ, 2 ≤ σ ∧ σ < σs ∧ max (nuR r 1 n) (nuR r 2 n) < muR r {σ} (n + 1))

theorem muR_empty_eq {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) : muR r ∅ n = nuR r 1 n := by
  rw [← muR_prefix hr le_rfl hn, Nat.sub_self, add_zero,
    Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num)]

theorem muR_one_eq {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) :
    muR r {1} (n + 1) = nuR r 2 n := by
  rw [← muR_prefix hr (by norm_num : 1 ≤ 2) hn, show (2 : ℕ) - 1 = 1 from rfl, Finset.Icc_self]

/-- `η_σ(n) ≤ Φ_r((1 - s/σ) p) = Φ_r(p) - (Ψ_r(p) - 2R_p(σ))/σ`. -/
theorem etaR_le {r : ℝ} (hr : 1 < r) {n : ℕ} {p : ℝ[X]} (hp : p.degree < n)
    (hp0 : p.eval 0 = 1) {σ : ℕ} (hσ : 1 ≤ σ) :
    muR r {σ} (n + 1) ≤ rowPhi r p - (psiR r p - 2 * remR r p σ) / σ := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  rw [← rowPhi_mul_lin hr p hσ0]
  have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
  have hpn : p.natDegree < n := by
    rw [degree_eq_natDegree hpne] at hp
    exact_mod_cast hp
  have hlin : (1 - C (1 / (σ : ℝ)) * X).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; omega)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  unfold muR
  refine ciInf_le ⟨0, ?_⟩ (⟨p * (1 - C (1 / (σ : ℝ)) * X), ?_, ?_, fun s hs => ?_⟩ :
    {q : ℝ[X] // q.degree < ↑(n + 1) ∧ q.eval 0 = 1 ∧
      ∀ s ∈ ({σ} : Finset ℕ), q.eval (s : ℝ) = 0})
  · rintro _ ⟨q, rfl⟩
    exact tsum_nonneg fun _ => by positivity
  · refine degree_le_natDegree.trans_lt ?_
    have := natDegree_mul_le (p := p) (q := 1 - C (1 / (σ : ℝ)) * X)
    exact_mod_cast (show (p * (1 - C (1 / (σ : ℝ)) * X)).natDegree < n + 1 by omega)
  · rw [eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zero, sub_zero, mul_one, hp0]
  · rw [Finset.mem_singleton.1 hs, eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X,
      one_div_mul_cancel hσ0.ne', sub_self, mul_zero]

theorem secondRow : SecondRow := by
  intro r hr n hn
  have hν1 := nuR_pos hr le_rfl hn
  have hν2 := nuR_pos hr (by norm_num : 1 ≤ 2) hn
  have hη : ∀ σ : ℕ, 1 ≤ σ → 0 < muR r {σ} (n + 1) := fun σ hσ =>
    muR_pos hr (by rw [Finset.mem_singleton]; omega) (by rw [Finset.card_singleton]; omega)
  have hbdd : BddBelow (Set.range fun S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = 2} =>
      1 / muR r S.1 (n + 1)) := ⟨0, by
    rintro _ ⟨S, rfl⟩
    exact one_div_nonneg.2 (muR_nonneg hr _ _)⟩
  have hVdual := (rowValueDual r hr).1 (n + 1) 2 (by norm_num) (by omega)
  -- `V ≤ 1/η_σ` and `V ≤ 1/ν_1`
  have hVη : ∀ σ : ℕ, 1 ≤ σ → rowValue r (n + 1) 2 ≤ 1 / muR r {σ} (n + 1) := fun σ hσ => by
    rw [hVdual]
    exact ciInf_le hbdd ⟨{σ}, by rw [Finset.mem_singleton]; omega, by rw [Finset.card_singleton]⟩
  have hVν : rowValue r (n + 1) 2 ≤ 1 / nuR r 1 n := by
    have := rowValue_le_top hr (by norm_num : 1 ≤ 2) (by omega : 2 ≤ n + 1)
    rwa [show n + 1 - 2 + 1 = n by omega, muR_empty_eq hr hn] at this
  refine ⟨fun p hp hp0 σ hσ => etaR_le hr hp hp0 hσ, ?_, fun p hp hp0 hpν => ?_⟩
  · obtain ⟨q, hq, hq0, -, hqΦ⟩ := exists_muR_min hr (S := ∅) (L := n)
      (Finset.notMem_empty 0) (by rw [Finset.card_empty]; omega)
    exact ⟨q, hq, hq0, by rw [hqΦ, muR_empty_eq hr hn]⟩
  have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
  classical
  let σs := Nat.find (exists_sigma_star hr hpne)
  obtain ⟨hσs1, hσsR⟩ := Nat.find_spec (exists_sigma_star hr hpne)
  have hbelow : ∀ σ : ℕ, 1 ≤ σ → σ < σs → psiR r p < 2 * remR r p σ := fun σ h1 hlt => by
    have := Nat.find_min (exists_sigma_star hr hpne) hlt
    push_neg at this
    exact this h1
  have hfar : ∀ σ : ℕ, σs ≤ σ → muR r {σ} (n + 1) ≤ nuR r 1 n := fun σ hσ => by
    have hR := remR_anti hr p (Nat.cast_nonneg σs) (show (σs : ℝ) ≤ σ by exact_mod_cast hσ)
    have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
    refine (etaR_le hr hp hp0 (by omega)).trans ?_
    rw [hpν, sub_le_self_iff]
    exact div_nonneg (by linarith) hσ0.le
  have hfar' : ∀ σ : ℕ, σs < σ → muR r {σ} (n + 1) < nuR r 1 n := fun σ hσ => by
    have hR := remR_anti hr p (Nat.cast_nonneg (σs + 1))
      (show ((σs + 1 : ℕ) : ℝ) ≤ σ by exact_mod_cast hσ)
    have hR' := remR_succ_lt hr hpne σs
    have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
    refine (etaR_le hr hp hp0 (by omega)).trans_lt ?_
    rw [hpν, sub_lt_self_iff]
    exact div_pos (by linarith) hσ0
  have hV : rowValue r (n + 1) 2 =
      (Finset.Ico 1 σs).fold min (1 / nuR r 1 n) (fun σ => 1 / muR r {σ} (n + 1)) := by
    refine le_antisymm
      ((Finset.le_fold_min _).2 ⟨hVν, fun σ hσ => hVη σ (Finset.mem_Ico.1 hσ).1⟩) ?_
    rw [hVdual]
    haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = 2} :=
      ⟨⟨{1}, by rw [Finset.mem_singleton]; omega, by rw [Finset.card_singleton]⟩⟩
    refine le_ciInf fun S => ?_
    obtain ⟨σ, hσS⟩ := Finset.card_eq_one.1 (show S.1.card = 1 by have := S.2.2; omega)
    have hσ1 : 1 ≤ σ := by
      have := S.2.1
      rw [hσS, Finset.mem_singleton] at this
      omega
    rw [hσS]
    rcases lt_or_ge σ σs with h | h
    · exact (Finset.fold_min_le _).2 (Or.inr ⟨σ, Finset.mem_Ico.2 ⟨hσ1, h⟩, le_rfl⟩)
    · exact (Finset.fold_min_le _).2 (Or.inl (one_div_le_one_div_of_le (hη σ hσ1) (hfar σ h)))
  refine ⟨σs, hσs1, hσsR, hbelow, hfar, hfar', hV, ?_⟩
  have hVν2 : rowValue r (n + 1) 2 ≤ 1 / nuR r 2 n := by
    rw [← muR_one_eq hr hn]
    exact hVη 1 le_rfl
  constructor
  · intro hne
    by_contra hno
    push_neg at hno
    refine hne (le_antisymm (le_min hVν hVν2) ?_)
    rw [hV]
    refine (Finset.le_fold_min _).2 ⟨min_le_left _ _, fun σ hσ => ?_⟩
    obtain ⟨hσ1, hσlt⟩ := Finset.mem_Ico.1 hσ
    rcases Nat.lt_or_ge σ 2 with h2 | h2
    · rw [show σ = 1 by omega, muR_one_eq hr hn]
      exact min_le_right _ _
    · have hle := one_div_le_one_div_of_le (hη σ hσ1) (hno σ h2 hσlt)
      refine le_trans ?_ hle
      rcases le_total (nuR r 1 n) (nuR r 2 n) with h | h
      · rw [max_eq_right h]
        exact min_le_right _ _
      · rw [max_eq_left h]
        exact min_le_left _ _
  · rintro ⟨σ, h2, -, hmax⟩
    refine ne_of_lt (lt_of_le_of_lt (hVη σ (by omega)) (lt_min ?_ ?_))
    · exact one_div_lt_one_div_of_lt hν1 ((le_max_left _ _).trans_lt hmax)
    · exact one_div_lt_one_div_of_lt hν2 ((le_max_right _ _).trans_lt hmax)

end CoefficientMass
