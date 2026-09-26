/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowFar

/-!
# Dropping a Far Exempted Position

This module proves Lemma 6.10 of `coefficient-mass-rows.tex`: `V_r(L, k) ≤ V_r(L - 1, k - 1)`.
For `|S'| = k - 2`, exempting `S'` and one far position gives
`V_r(L, k) ≤ 1/μ_r(S', L - 1)` (`rowValue_le_base`), and the infimum over `S'` is
`V_r(L - 1, k - 1)` by Proposition 2.1(b).

## Definitions

* `RowMono`.

## Theorems

* `rowMono`.
-/

namespace CoefficientMass

/-- Lemma 6.10 of `coefficient-mass-rows.tex`: for `r > 1` and `2 ≤ k ≤ L`,
`V_r(L, k) ≤ V_r(L - 1, k - 1)`; so `V_r(n + k - 1, k)` does not increase with `k`. -/
def RowMono : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ L k : ℕ, 2 ≤ k → k ≤ L → rowValue r L k ≤ rowValue r (L - 1) (k - 1)) ∧
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → rowValue r (n + (k + 1) - 1) (k + 1) ≤ rowValue r (n + k - 1) k

theorem rowMono : RowMono := by
  intro r hr
  have h1 : ∀ L k : ℕ, 2 ≤ k → k ≤ L → rowValue r L k ≤ rowValue r (L - 1) (k - 1) := by
    intro L k hk hkL
    rw [(rowValueDual r hr).1 (L - 1) (k - 1) (by omega) (by omega)]
    haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k - 1} :=
      ⟨⟨Finset.Icc 1 (k - 2), fun h => by have := (Finset.mem_Icc.1 h).1; omega,
        by rw [Nat.card_Icc]; omega⟩⟩
    refine le_ciInf fun S => ?_
    have hS := S.2.2
    have := rowValue_le_base hr (by omega : 1 ≤ k) hkL S.2.1 (by omega)
    rwa [show L - (k - 1 - S.1.card) = L - 1 by omega] at this
  refine ⟨h1, fun n k hn hk => ?_⟩
  have := h1 (n + (k + 1) - 1) (k + 1) (by omega) (by omega)
  rwa [show n + (k + 1) - 1 - 1 = n + k - 1 by omega, Nat.add_sub_cancel] at this

end CoefficientMass
