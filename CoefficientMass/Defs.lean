/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Coefficient Mass Definitions

This module fixes the quantities the paper `coefficient-mass.tex` bounds, so
that every later statement reads them from one place: the logarithmic
coefficient mass `Λ(F) = ∑ log⁺ |f_j|`, the count of large nonleading
coefficients that stands in for the order statistics `b_k`, and the monic
polynomial with prescribed real roots.

The order statistic `b_k(F)` is the `k`-th largest of `|f_j|`, `j < deg F`.
Rather than sort, the statements use the equivalent form the paper's own proof
of Theorem 3.2 uses: `b_k(F) ≥ T` exactly when at least `k` positions `j < deg F`
have `|f_j| ≥ T`.

## Definitions

* `logPlus`.
* `mass`.
* `largeCount`.
* `rootProduct`.

## Theorems

* `logPlus_nonneg`.
* `mass_nonneg`.
-/

open Polynomial

namespace CoefficientMass

/-- `log⁺ x = max 0 (log x)`, which ignores magnitudes at most one. -/
noncomputable def logPlus (x : ℝ) : ℝ :=
  max 0 (Real.log x)

/-- The logarithmic coefficient mass `Λ(F) = ∑_{f_j ≠ 0} log⁺ |f_j|`, the
logarithm of the multiplicative height. -/
noncomputable def mass (F : ℂ[X]) : ℝ :=
  ∑ j ∈ F.support, logPlus ‖F.coeff j‖

/-- The number of nonleading positions `j < deg F` with `|f_j| ≥ T`; the order
statistic `b_k(F)` is at least `T` exactly when this is at least `k`. -/
noncomputable def largeCount {R : Type*} [Semiring R] [Norm R] (F : R[X]) (T : ℝ) : ℕ :=
  ((Finset.range F.natDegree).filter fun j => T ≤ ‖F.coeff j‖).card

/-- The monic polynomial `∏ (x - r_i)` with the prescribed real roots, over any
field `𝕜` receiving the reals. -/
noncomputable def rootProduct {L : ℕ} (𝕜 : Type*) [Field 𝕜] [Algebra ℝ 𝕜]
    (r : Fin L → ℝ) : 𝕜[X] :=
  ∏ i, (X - C (algebraMap ℝ 𝕜 (r i)))

theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x :=
  le_max_left 0 (Real.log x)

theorem mass_nonneg (F : ℂ[X]) : 0 ≤ mass F :=
  Finset.sum_nonneg fun j _ => logPlus_nonneg ‖F.coeff j‖

end CoefficientMass
