/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Defs

/-!
# Coefficient Order Statistics and Mass

This module states Section 3 of `coefficient-mass.tex` as propositions, down
to Corollary 3.4, the bound `bangyen/esolangs` cites for the Polynomial
language.  Roots are indexed from zero, so the paper's `r_{u+1}, …, r_L` are
the indices `i ≥ u` here and the weight `i` in the mass bound is `i + 1`.

The chain these statements form is
`ZeroBound → ConsecutiveTail, TailBound → CertificateWithExclusions →
OrderStatistics → ComplexOrderStatistics → LogarithmicMass`.
The clauses of Lemma 3.1 and Theorem 3.2 that relax `r_1 ≥ 2` to `r_1 > 1`
for the first row are stated and proved separately, in `FirstRow`: Corollary
3.4 does not use them.

## Definitions

* `CertificateWithExclusions`.
* `OrderStatistics`.
* `ComplexOrderStatistics`.
* `LogarithmicMass`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 3.1 (certificate with excluded positions): for distinct roots
`2 ≤ r_1 < ⋯ < r_L` and a real multiple `F` with `|f_D| = 1`, any `u < L`
positions below `D` miss some `j < D` with `|f_j| ≥ ∏_{i > u} (r_i - 1)`. -/
def CertificateWithExclusions : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]) (U : Finset ℕ),
    StrictMono r → (∀ i, 2 ≤ r i) → rootProduct ℝ r ∣ F → ‖F.leadingCoeff‖ = 1 →
    U.card < L → U ⊆ Finset.range F.natDegree →
      ∃ j < F.natDegree, j ∉ U ∧
        ∏ i ∈ Finset.univ.filter (fun i : Fin L => U.card ≤ i.val), (r i - 1) ≤
          ‖F.coeff j‖

/-- Theorem 3.2 (coefficient order statistics): for real roots
`2 ≤ r_1 ≤ ⋯ ≤ r_L`, repetitions allowed, and a nonzero real multiple `F`,
`b_{u+1}(F) ≥ |f_D| ∏_{i > u} (r_i - 1)` for every `u < L`. -/
def OrderStatistics : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]),
    Monotone r → (∀ i, 2 ≤ r i) → F ≠ 0 → rootProduct ℝ r ∣ F →
      ∀ u : Fin L, u.val + 1 ≤
        largeCount F (‖F.leadingCoeff‖ * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1))

/-- Corollary 3.3 (complex multiples): `OrderStatistics` for a nonzero complex
multiple of the same real-rooted product. -/
def ComplexOrderStatistics : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℂ[X]),
    Monotone r → (∀ i, 2 ≤ r i) → F ≠ 0 → rootProduct ℂ r ∣ F →
      ∀ u : Fin L, u.val + 1 ≤
        largeCount F (‖F.leadingCoeff‖ * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1))

/-- Corollary 3.4 (logarithmic mass): for real roots `2 ≤ r_1 ≤ ⋯ ≤ r_L` and a
nonzero complex multiple `F`,
`Λ(F) ≥ (L + 1) log |f_D| + ∑ i log (r_i - 1)`.  A real multiple is covered
through `Polynomial.map (algebraMap ℝ ℂ)`. -/
def LogarithmicMass : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ) (F : ℂ[X]),
    Monotone r → (∀ i, 2 ≤ r i) → F ≠ 0 → rootProduct ℂ r ∣ F →
      (L + 1) * Real.log ‖F.leadingCoeff‖ +
        ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) ≤ mass F

end CoefficientMass
