/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowCert
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Polynomials Vanishing on a Far Block

This module prepares Proposition 2.1(c) of `coefficient-mass-rows.tex`.  A real `q` with
`deg q < L`, `q(0) = 1` and `q = 0` on the block `S_N = [N + 1, N + m]` factors as
`q = r_{S_N} q_0` with `deg q_0 + m < L` and `q_0(0) = 1`, and for `1 ≤ s ≤ M ≤ N`,
`r_{S_N}(s) ≥ (1 - M/N)^m`.

## Theorems

* `eval_confPolyP`.
* `factor_far`.
* `confPolyP_far_ge`.
-/

open Polynomial

namespace CoefficientMass

theorem eval_confPolyP (Z : Finset ℕ) (y : ℝ) :
    (confPolyP Z).eval y = ∏ z ∈ Z, (1 - y / z) := by
  rw [confPolyP, eval_prod]
  exact Finset.prod_congr rfl fun z _ => by rw [eval_add, eval_mul, eval_C, eval_C, eval_X]; ring

/-- `q = r_{S_N} q_0` with `deg q_0 + m < L` and `q_0(0) = 1`. -/
theorem factor_far {N m L : ℕ} {q : ℝ[X]} (hq : q.degree < L) (hq0 : q.eval 0 = 1)
    (hqS : ∀ s ∈ Finset.Icc (N + 1) (N + m), q.eval (s : ℝ) = 0) :
    ∃ q₀ : ℝ[X], q₀.natDegree + m < L ∧ q₀.eval 0 = 1 ∧
      ∀ y : ℝ, q.eval y = (confPolyP (Finset.Icc (N + 1) (N + m))).eval y * q₀.eval y := by
  set T := Finset.Icc (N + 1) (N + m)
  set P := ∏ σ ∈ T, (X - C (σ : ℝ))
  have hcop := pairwise_coprime_X_sub_C (s := fun σ : ℕ => (σ : ℝ)) Nat.cast_injective
  have hdvd : P ∣ q := Finset.prod_dvd_of_coprime (fun i _ j _ hij => hcop hij)
    fun σ hσ => dvd_iff_isRoot.2 (hqS σ hσ)
  obtain ⟨q₁, hq₁⟩ := hdvd
  have hσ0 : ∀ σ ∈ T, (σ : ℝ) ≠ 0 := fun σ hσ => by
    have := (Finset.mem_Icc.1 hσ).1
    exact_mod_cast (show σ ≠ 0 by omega)
  have hP0 : P.eval 0 ≠ 0 := by
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ hσ => by
      rw [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
      exact hσ0 σ hσ
  have hPy : ∀ y : ℝ, P.eval y = (confPolyP T).eval y * P.eval 0 := fun y => by
    rw [eval_confPolyP, eval_prod, eval_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun σ hσ => ?_
    rw [eval_sub, eval_X, eval_C, eval_sub, eval_X, eval_C, one_sub_div (hσ0 σ hσ), zero_sub,
      div_mul_eq_mul_div, mul_neg, neg_div, mul_div_cancel_right₀ _ (hσ0 σ hσ), neg_sub]
  refine ⟨C (P.eval 0) * q₁, ?_, ?_, fun y => ?_⟩
  · have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
    have hPne : P ≠ 0 := fun h => hP0 (by rw [h, eval_zero])
    have hq₁ne : q₁ ≠ 0 := fun h => hqne (by rw [hq₁, h, mul_zero])
    have hdeg : q.natDegree = m + q₁.natDegree := by
      rw [hq₁, natDegree_mul hPne hq₁ne, natDegree_finset_prod_X_sub_C_eq_card, Nat.card_Icc]
      omega
    have hqL : q.natDegree < L := by
      rw [degree_eq_natDegree hqne] at hq
      exact_mod_cast hq
    have := natDegree_C_mul_le (P.eval 0) q₁
    omega
  · rw [eval_mul, eval_C, ← eval_mul, ← hq₁, hq0]
  · rw [hq₁, eval_mul, hPy, eval_mul, eval_C]
    ring

/-- `r_{[N + 1, N + m]}(s) ≥ (1 - M/N)^m` for `s ≤ M ≤ N`, `N > 0`. -/
theorem confPolyP_far_ge {N m M s : ℕ} (hN : 0 < N) (hsM : s ≤ M) (hMN : M ≤ N) :
    (1 - (M : ℝ) / N) ^ m ≤ (confPolyP (Finset.Icc (N + 1) (N + m))).eval (s : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 ≤ 1 - (M : ℝ) / N := by
    rw [sub_nonneg, div_le_one hN']
    exact_mod_cast hMN
  rw [eval_confPolyP]
  calc (1 - (M : ℝ) / N) ^ m = ∏ _σ ∈ Finset.Icc (N + 1) (N + m), (1 - (M : ℝ) / N) := by
        rw [Finset.prod_const, Nat.card_Icc, show N + m + 1 - (N + 1) = m by omega]
    _ ≤ ∏ σ ∈ Finset.Icc (N + 1) (N + m), (1 - (s : ℝ) / σ) :=
        Finset.prod_le_prod (fun _ _ => hc) fun σ hσ => by
          have hσN : (N : ℝ) ≤ σ := by
            have := (Finset.mem_Icc.1 hσ).1
            exact_mod_cast (show N ≤ σ by omega)
          have hsM' : (s : ℝ) ≤ M := by exact_mod_cast hsM
          have h1 : (s : ℝ) / σ ≤ M / σ :=
            div_le_div_of_nonneg_right hsM' (hN'.le.trans hσN)
          have h2 : (M : ℝ) / σ ≤ M / N :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg M) hN' hσN
          linarith

end CoefficientMass
