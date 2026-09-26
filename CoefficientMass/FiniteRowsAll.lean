/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FiniteRowsB

/-!
# Every Row Is a Finite Minimum: Statement

This module states Theorem 6.19 of `coefficient-mass-rows.tex` in full, from its two parts
`finiteRowsA` and `finiteRowsB`.

## Definitions

* `FiniteRows`.

## Theorems

* `finiteRows`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 6.19 of `coefficient-mass-rows.tex`: for `r > 1` and `n, m ≥ 1`, (a) with minimizers
`q_N` of `μ_r(N, n + |N|)` and `T(N) = t_{m-|N|}(q_N)`, the good sets `𝒮` of size `m` form a
finite family and `V_r(n + m, m + 1) = min(V_r(n + m - 1, m), min_{S ∈ 𝒮} 1/μ_r(S, n + m))`;
(b) a finite tree `𝒯` of admissible `q_N` with `Φ_r(q_N) ≤ B` and thresholds `T_N` bounds every
`μ_r(S, n + m)` by `B`, so `V_r(n + m, m + 1) ≥ 1/B`. -/
def FiniteRows : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (∀ qN : Finset ℕ → ℝ[X], (∀ N : Finset ℕ, 0 ∉ N → N.card < m →
        (qN N).degree < n + N.card ∧ (qN N).eval 0 = 1 ∧ (∀ s ∈ N, (qN N).eval (s : ℝ) = 0) ∧
          rowPhi r (qN N) = muR r N (n + N.card)) →
      (goodSets (fun N => tM r (qN N) (m - N.card)) m).Finite ∧
        ∀ F : Finset (Finset ℕ),
          (F : Set (Finset ℕ)) = goodSets (fun N => tM r (qN N) (m - N.card)) m →
            rowValue r (n + m) (m + 1) =
              F.fold min (rowValue r (n + m - 1) m) (fun S => 1 / muR r S (n + m))) ∧
    ∀ (B : ℝ) (𝒯 : Set (Finset ℕ)) (qN : Finset ℕ → ℝ[X]) (TN : Finset ℕ → ℕ),
      ∅ ∈ 𝒯 → (∀ N ∈ 𝒯, N.card < m) →
      (∀ N ∈ 𝒯, (qN N).degree < n + N.card ∧ (qN N).eval 0 = 1 ∧
        (∀ s ∈ N, (qN N).eval (s : ℝ) = 0) ∧ rowPhi r (qN N) ≤ B ∧ 1 ≤ TN N ∧
          deltaQ r (qN N) (m - N.card) (TN N) ≤ 0) →
      (∀ N ∈ 𝒯, N.card + 2 ≤ m → ∀ σ : ℕ, N.sup id < σ → σ < TN N → insert σ N ∈ 𝒯) →
      (∀ N ∈ 𝒯, N.card + 1 = m → ∀ σ : ℕ, N.sup id < σ → σ < TN N →
        muR r (insert σ N) (n + m) ≤ B) →
      (∀ S : Finset ℕ, 0 ∉ S → S.card = m → muR r S (n + m) ≤ B) ∧
        1 / B ≤ rowValue r (n + m) (m + 1)

theorem finiteRows : FiniteRows := fun _ hr _ _ hn hm =>
  ⟨fun qN hqN => finiteRowsA hr hn hm qN hqN,
    fun _ 𝒯 qN TN hT0 hTc hq hstep hleaf => finiteRowsB hr hn 𝒯 hT0 hTc qN TN hq hstep hleaf⟩

end CoefficientMass
