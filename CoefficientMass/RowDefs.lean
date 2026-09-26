/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Rows at the Root Two

This module states Section 4.4 of `coefficient-mass.tex`, the `D`-free form
of the rows, as propositions.  At a single root `2` of multiplicity `L` the
certificates of Section 3 are replaced by their confluent limits
`r_Z(s) 2^{-s}` with `r_Z(s) = ∏_{z ∈ Z} (1 - s / z)`, and the row
`b_k ≥ L - k + 1` reduces to the statement `(∗_n)` about
`Φ(Z) = ∑_{s ≥ 1} |r_Z(s)| 2^{-s}`.

## Definitions

* `confPoly`.
* `confTail`.
* `Star`.
* `RowCertificate`.
* `EveryRow`.
-/

open Polynomial

namespace CoefficientMass

/-- The confluent certificate `r_Z(s) = ∏_{z ∈ Z} (1 - s / z)`. -/
noncomputable def confPoly (Z : Finset ℕ) (s : ℕ) : ℝ :=
  ∏ z ∈ Z, (1 - (s : ℝ) / z)

/-- `Φ(Z) = ∑_{s ≥ 1} |r_Z(s)| 2^{-s}`, indexed from `s = d + 1`. -/
noncomputable def confTail (Z : Finset ℕ) : ℝ :=
  ∑' d : ℕ, |confPoly Z (d + 1)| * (1 / 2) ^ (d + 1)

/-- The statement `(∗_n)`: every finite `A ⊂ ℕ_{>0}` lies in a finite `Z` with
`|Z| ≤ |A| + n - 1` and `Φ(Z) ≤ 1 / n`. -/
def Star (n : ℕ) : Prop :=
  ∀ A : Finset ℕ, 0 ∉ A →
    ∃ Z : Finset ℕ, A ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 ≤ A.card + n ∧ confTail Z ≤ 1 / n

/-- Lemma 4.5 (certificate for a row): for a monic multiple `F` of `(x - 2)^L`
and `1 ≤ k ≤ L`, if every set `S` of `k - 1` backward distances lies in a
`Z ⊂ ℕ_{>0}` with `|Z| ≤ L - 1` and `Φ(Z) ≤ 1 / n`, `n = L - k + 1`, then
`b_k(F) ≥ n`. -/
def RowCertificate : Prop :=
  ∀ (L k : ℕ) (F : ℝ[X]), F.Monic → (X - C 2) ^ L ∣ F → 1 ≤ k → k ≤ L →
    (∀ S : Finset ℕ, 0 ∉ S → S.card + 1 = k →
      ∃ Z : Finset ℕ, S ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 ≤ L ∧ confTail Z ≤ 1 / (L - k + 1 : ℕ)) →
      k ≤ largeCount F (L - k + 1 : ℕ)

/-- Theorem 4.13 (every row at the root `2`): every monic multiple `F` of
`(x - 2)^L` has `b_k(F) ≥ L - k + 1` for `1 ≤ k ≤ L`. -/
def EveryRow : Prop :=
  ∀ (L k : ℕ) (F : ℝ[X]), F.Monic → (X - C 2) ^ L ∣ F → 1 ≤ k → k ≤ L →
    k ≤ largeCount F (L - k + 1 : ℕ)

end CoefficientMass
