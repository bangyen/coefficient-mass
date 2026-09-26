/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ExpSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Worked Examples of Section 2

This module checks the examples after Theorem 2.2 of `coefficient-mass.tex`.  At the nodes
`(1/3, 1/2)` the zero sets `{1}` and `{2}` give the tails `1/2` and `3/10`; at `(1/5, 1/3)`
they give `1/8` and `9/64`; and at `(1/10, 4/5)`, outside the range of Theorem 2.2, the
zero set `{2}` gives `52/405 > 1/9`.  For two nodes `y < z` with `a ≥ 0` the sign of
`a y^n + b z^n` is fixed once it is at most zero at `n = 2`, so each tail is `|w_1|` plus a
difference of two geometric series.

## Definitions

* `WorkedExamples`.

## Theorems

* `neg_of_base`.
* `tail_two`.
* `workedExamples`.
-/

namespace CoefficientMass

/-- The certificates and tails of the examples after Theorem 2.2: `1/2`, `3/10`, `1/8`,
`9/64` and `52/405`. -/
def WorkedExamples : Prop :=
  (IsCertificate (![3, -2] : Fin 2 → ℝ) ![1 / 3, 1 / 2] {1} ∧
    HasSum (fun d => |expSum (![3, -2] : Fin 2 → ℝ) ![1 / 3, 1 / 2] (d + 1)|) (1 / 2)) ∧
  (IsCertificate (![9 / 5, -4 / 5] : Fin 2 → ℝ) ![1 / 3, 1 / 2] {2} ∧
    HasSum (fun d => |expSum (![9 / 5, -4 / 5] : Fin 2 → ℝ) ![1 / 3, 1 / 2] (d + 1)|)
      (3 / 10)) ∧
  (IsCertificate (![5 / 2, -3 / 2] : Fin 2 → ℝ) ![1 / 5, 1 / 3] {1} ∧
    HasSum (fun d => |expSum (![5 / 2, -3 / 2] : Fin 2 → ℝ) ![1 / 5, 1 / 3] (d + 1)|)
      (1 / 8)) ∧
  (IsCertificate (![25 / 16, -9 / 16] : Fin 2 → ℝ) ![1 / 5, 1 / 3] {2} ∧
    HasSum (fun d => |expSum (![25 / 16, -9 / 16] : Fin 2 → ℝ) ![1 / 5, 1 / 3] (d + 1)|)
      (9 / 64)) ∧
  (IsCertificate (![64 / 63, -1 / 63] : Fin 2 → ℝ) ![1 / 10, 4 / 5] {2} ∧
    HasSum (fun d => |expSum (![64 / 63, -1 / 63] : Fin 2 → ℝ) ![1 / 10, 4 / 5] (d + 1)|)
      (52 / 405))

/-- Once `a y^{n_0} + b z^{n_0} ≤ 0` with `0 ≤ a` and `0 ≤ y ≤ z`, it stays so. -/
theorem neg_of_base {a b y z : ℝ} {n₀ : ℕ} (ha : 0 ≤ a) (hy0 : 0 ≤ y) (hyz : y ≤ z)
    (hbase : a * y ^ n₀ + b * z ^ n₀ ≤ 0) (k : ℕ) :
    a * y ^ (n₀ + k) + b * z ^ (n₀ + k) ≤ 0 := by
  have hk : y ^ k ≤ z ^ k := pow_le_pow_left₀ hy0 hyz k
  have h1 : a * y ^ n₀ * y ^ k ≤ a * y ^ n₀ * z ^ k :=
    mul_le_mul_of_nonneg_left hk (mul_nonneg ha (pow_nonneg hy0 _))
  have h2 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (hy0.trans hyz) k) hbase
  rw [pow_add, pow_add]
  nlinarith

/-- `∑_{d ≥ 1} |a y^d + b z^d| = |a y + b z| - (a y^2 / (1 - y) + b z^2 / (1 - z))` when
`a y^d + b z^d ≤ 0` for `d ≥ 2`. -/
theorem tail_two {a b y z T : ℝ} (ha : 0 ≤ a) (hy0 : 0 ≤ y) (hyz : y ≤ z) (hz1 : z < 1)
    (hbase : a * y ^ 2 + b * z ^ 2 ≤ 0)
    (hT : T = |a * y + b * z| - (a * y ^ 2 / (1 - y) + b * z ^ 2 / (1 - z))) :
    HasSum (fun d => |a * y ^ (d + 1) + b * z ^ (d + 1)|) T := by
  have h1 := (hasSum_geometric_of_lt_one hy0 (hyz.trans_lt hz1)).mul_left (a * y ^ 2)
  have h2 := (hasSum_geometric_of_lt_one (hy0.trans hyz) hz1).mul_left (b * z ^ 2)
  have h := (h1.add h2).neg
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.sum_range_one, Nat.zero_add, pow_one]
  rw [hT]
  convert h using 1
  · funext d
    rw [show d + 1 + 1 = 2 + d by omega, abs_of_nonpos (neg_of_base ha hy0 hyz hbase d),
      pow_add, pow_add]
    ring
  · ring

theorem workedExamples : WorkedExamples := by
  have e : ∀ (a b y z : ℝ) (d : ℕ), expSum ![a, b] ![y, z] d = a * y ^ d + b * z ^ d :=
    fun a b y z d => by
      simp only [expSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  simp only [IsCertificate, e, Finset.mem_singleton, forall_eq]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, tail_two (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [abs_of_nonneg (by norm_num)]; norm_num)⟩,
    ⟨⟨by norm_num, by norm_num⟩, tail_two (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [abs_of_nonneg (by norm_num)]; norm_num)⟩,
    ⟨⟨by norm_num, by norm_num⟩, tail_two (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [abs_of_nonneg (by norm_num)]; norm_num)⟩,
    ⟨⟨by norm_num, by norm_num⟩, tail_two (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [abs_of_nonneg (by norm_num)]; norm_num)⟩,
    ⟨⟨by norm_num, by norm_num⟩, tail_two (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [abs_of_nonneg (by norm_num)]; norm_num)⟩⟩

end CoefficientMass
