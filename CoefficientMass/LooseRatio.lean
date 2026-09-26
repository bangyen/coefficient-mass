/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Ratio in Proposition 4.1

This module proves the last clause of Proposition 4.1 of `coefficient-mass.tex`: for
`r_i = 2 + i L^{-3}`, `i = 1, …, L`, the ratio `S / (B + 1)` between the certificate bound
and `B = |P(1)|` is at least `L / 2`, so it is unbounded in `L`.  Here `S ≥ 2L` and
`B = ∏ (1 + i L^{-3}) ≤ exp (∑ i L^{-3}) ≤ e < 3`.

## Definitions

* `LooseRatio`.

## Theorems

* `looseRatio`.
-/

namespace CoefficientMass

/-- For `r_i = 2 + i L^{-3}`, `S / (B + 1) ≥ L / 2`. -/
def LooseRatio : Prop :=
  ∀ L : ℕ, 1 ≤ L → (L : ℝ) / 2 ≤ (∑ i : Fin L, (2 + ((i : ℕ) + 1 : ℝ) / (L : ℝ) ^ 3)) /
    (∏ i : Fin L, (2 + ((i : ℕ) + 1 : ℝ) / (L : ℝ) ^ 3 - 1) + 1)

theorem looseRatio : LooseRatio := by
  intro L hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  set x : Fin L → ℝ := fun i => ((i : ℕ) + 1 : ℝ) / (L : ℝ) ^ 3 with hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => by positivity
  have hxL : ∀ i, x i ≤ 1 / L := fun i => by
    have hi : ((i : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast i.isLt
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  have hS : 2 * (L : ℝ) ≤ ∑ i, (2 + x i) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      (by linarith [hx0 i] : (2 : ℝ) ≤ 2 + x i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hsum : ∑ i, x i ≤ 1 := by
    calc ∑ i, x i ≤ ∑ _i : Fin L, 1 / (L : ℝ) := Finset.sum_le_sum fun i _ => hxL i
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div_cancel hL0.ne']
  have hB : ∏ i, (2 + x i - 1) ≤ Real.exp 1 := by
    calc ∏ i, (2 + x i - 1) ≤ ∏ i, Real.exp (x i) :=
          Finset.prod_le_prod (fun i _ => by linarith [hx0 i]) fun i _ => by
            have := Real.add_one_le_exp (x i)
            linarith
      _ = Real.exp (∑ i, x i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 hsum
  have he := Real.exp_one_lt_d9
  have hB0 : 0 ≤ ∏ i, (2 + x i - 1) := Finset.prod_nonneg fun i _ => by linarith [hx0 i]
  have hLB := mul_le_mul_of_nonneg_left (hB.trans he.le) hL0.le
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end CoefficientMass
