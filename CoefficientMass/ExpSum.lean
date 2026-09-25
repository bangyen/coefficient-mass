/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exponential Sums and the Displaced-Zero Tail

This module states Section 2 of `coefficient-mass.tex` as propositions: the
zero bound for exponential sums, the consecutive zero set (Lemma 2.1), and
the displaced-zero tail bound (Theorem 2.2).  Each is a `Prop`-valued
definition, so the library builds with no placeholder proofs; a statement is
proved by adding a theorem of that type.

An exponential sum on nodes `y_1 < ⋯ < y_c` is `w_d = ∑ a_i y_i^d`.  A
certificate for a zero set `Z` has `w_0 = 1` and `w_z = 0` on `Z`, and its
tail is `∑_{d ≥ 1} |w_d|`.  Every tail statement asserts summability, since
an infinite sum that does not converge is zero in Lean and would satisfy any
upper bound vacuously.

The paper's Theorem 2.2 also characterizes equality; only the inequality is
stated, since the coefficient bounds use nothing more.

## Definitions

* `expSum`.
* `IsCertificate`.
* `nodeProduct`.
* `ZeroBound`.
* `ConsecutiveTail`.
* `TailBound`.
-/

namespace CoefficientMass

/-- The exponential sum `w_d = ∑ a_i y_i^d` at an integer point `d`. -/
def expSum {c : ℕ} (a y : Fin c → ℝ) (d : ℕ) : ℝ :=
  ∑ i, a i * y i ^ d

/-- `a` is a certificate on the nodes `y` for the zero set `Z`: `w_0 = 1` and
`w_z = 0` for every `z ∈ Z`. -/
def IsCertificate {c : ℕ} (a y : Fin c → ℝ) (Z : Finset ℕ) : Prop :=
  expSum a y 0 = 1 ∧ ∀ z ∈ Z, expSum a y z = 0

/-- `∏_{i ≤ ℓ} y_i / (1 - y_i)` over the `ℓ + 1` smallest nodes, indexed from
zero; with `y_i = 1/ρ_i` this is `1 / ∏ (ρ_i - 1)`. -/
noncomputable def nodeProduct {c : ℕ} (y : Fin c → ℝ) (ℓ : ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin c => i.val ≤ ℓ), y i / (1 - y i)

/-- The zero bound: a nonzero exponential sum on `c` distinct positive nodes,
read as a function of a real variable, has at most `c - 1` real zeros.  The
count is `Set.encard`, which is infinite on an infinite set, so the bound also
asserts finiteness. -/
def ZeroBound : Prop :=
  ∀ (c : ℕ) (a y : Fin c → ℝ), Function.Injective y → (∀ i, 0 < y i) → a ≠ 0 →
    {t : ℝ | ∑ i, a i * y i ^ t = 0}.encard ≤ (c - 1 : ℕ)

/-- Lemma 2.1 (consecutive zero set): for nodes `0 < y_1 < ⋯ < y_c < 1` and
the zero set `{1, …, c - 1}`, the tail is exactly `∏ y_i / (1 - y_i)`. -/
def ConsecutiveTail : Prop :=
  ∀ (c : ℕ) (a y : Fin c → ℝ), StrictMono y → (∀ i, 0 < y i) → (∀ i, y i < 1) →
    IsCertificate a y (Finset.Ioo 0 c) →
      HasSum (fun d => |expSum a y (d + 1)|) (∏ i, y i / (1 - y i))

/-- Theorem 2.2 (displaced-zero tail bound): for nodes
`0 < y_1 < ⋯ < y_c ≤ 1/2`, a zero set `Z ⊆ ℕ_{>0}` of size `c - 1`, and any
`ℓ` with `{1, …, ℓ} ⊆ Z`, the tail is at most `∏_{i ≤ ℓ+1} y_i / (1 - y_i)`.
Quantifying over every such `ℓ` is equivalent to taking the leading run, since
each factor is at most one. -/
def TailBound : Prop :=
  ∀ (c : ℕ) (a y : Fin c → ℝ) (Z : Finset ℕ) (ℓ : ℕ),
    StrictMono y → (∀ i, 0 < y i) → (∀ i, y i ≤ 1 / 2) →
    0 ∉ Z → Z.card = c - 1 → Finset.Icc 1 ℓ ⊆ Z → IsCertificate a y Z →
      Summable (fun d => |expSum a y (d + 1)|) ∧
        ∑' d, |expSum a y (d + 1)| ≤ nodeProduct y ℓ

end CoefficientMass
