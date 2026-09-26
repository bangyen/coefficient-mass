/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly

/-!
# Monotone in the Root

This module proves Lemma 6.15 of `coefficient-mass-rows.tex`: for `1 < r ≤ r'`,
`Φ_{r'}(q) ≤ Φ_r(q)` term by term, and since the admissible set of `μ_r(S, L)` does not depend
on `r`, `μ_{r'}(S, L) ≤ μ_r(S, L)`; in particular `ν_i(n)` and `η_σ(n) = μ_r({σ}, n + 1)` do not
increase with `r`.

## Definitions

* `RootMono`.

## Theorems

* `rowPhi_anti`.
* `muR_anti`.
* `rootMono`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 6.15 of `coefficient-mass-rows.tex`: for `1 < r ≤ r'`, `Φ_{r'}(q) ≤ Φ_r(q)` for every
real `q`, `μ_{r'}(S, L) ≤ μ_r(S, L)`, and so `ν_i(n)` and `η_σ(n)` do not increase with `r`. -/
def RootMono : Prop :=
  ∀ r r' : ℝ, 1 < r → r ≤ r' →
    (∀ q : ℝ[X], rowPhi r' q ≤ rowPhi r q) ∧
    (∀ (S : Finset ℕ) (L : ℕ), muR r' S L ≤ muR r S L) ∧
    (∀ i n : ℕ, 1 ≤ i → 1 ≤ n → nuR r' i n ≤ nuR r i n) ∧
    ∀ σ n : ℕ, muR r' {σ} (n + 1) ≤ muR r {σ} (n + 1)

theorem rowPhi_anti {r r' : ℝ} (hr : 1 < r) (hrr : r ≤ r') (q : ℝ[X]) :
    rowPhi r' q ≤ rowPhi r q := by
  have hr' : 1 < r' := hr.trans_le hrr
  refine Summable.tsum_le_tsum (fun d => ?_) (summable_rowPhi hr' q) (summable_rowPhi hr q)
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (abs_nonneg _)
  exact one_div_le_one_div_of_le (by linarith) hrr

theorem muR_anti {r r' : ℝ} (hr : 1 < r) (hrr : r ≤ r') (S : Finset ℕ) (L : ℕ) :
    muR r' S L ≤ muR r S L := by
  rcases isEmpty_or_nonempty
    {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} with h | h
  · rw [muR, muR, Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
  · refine ciInf_mono ⟨0, ?_⟩ fun q => rowPhi_anti hr hrr q.1
    rintro _ ⟨q, rfl⟩
    exact tsum_nonneg fun _ => by
      have : 0 < 1 / r' := by have := hr.trans_le hrr; positivity
      positivity

theorem rootMono : RootMono := fun r r' hr hrr =>
  ⟨rowPhi_anti hr hrr, muR_anti hr hrr, fun i n hi hn => by
    rw [← muR_prefix (hr.trans_le hrr) hi hn, ← muR_prefix hr hi hn]
    exact muR_anti hr hrr _ _, fun σ n => muR_anti hr hrr _ _⟩

end CoefficientMass
