/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.PrefixWeights
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Shifting the Prefix Index

This module proves Lemma 6.3 of `coefficient-mass-rows.tex`.  By the convolution of the weights,
`A_{i+m}(p) = ∑_u ω_i(u) ∑_t ω_m(t) |p(u + t)|`, a rearrangement of nonnegative terms done in
`ℝ≥0∞`, and the inner sum is at least `ν_m(n) |p(u)|`.

## Definitions

* `PrefixShift`.

## Theorems

* `prefA_add_ge`.
* `prefixShift`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 6.3 of `coefficient-mass-rows.tex`: for `r > 1` and `n, i, m ≥ 1`,
`A_{i+m}(p) ≥ ν_m(n) A_i(p)` for real `p` with `deg p ≤ n - 1`; consequently
`ν_{i+m}(n) ≥ ν_i(n) ν_m(n)` and `ν_i(n) ≥ ν_1(n)^i`. -/
def PrefixShift : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n i m : ℕ, 1 ≤ n → 1 ≤ i → 1 ≤ m →
    (∀ p : ℝ[X], p.degree < n → nuR r m n * prefA r i p ≤ prefA r (i + m) p) ∧
    nuR r i n * nuR r m n ≤ nuR r (i + m) n ∧ nuR r 1 n ^ i ≤ nuR r i n

/-- `A_{i+m}(p) ≥ ν_m(n) A_i(p)`. -/
theorem prefA_add_ge {r : ℝ} (hr : 1 < r) {i m n : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (hn : 1 ≤ n)
    {p : ℝ[X]} (hp : p.degree < n) : nuR r m n * prefA r i p ≤ prefA r (i + m) p := by
  have hpn : p.natDegree < n := by
    by_cases hp0 : p = 0
    · rw [hp0, natDegree_zero]
      omega
    · rw [degree_eq_natDegree hp0] at hp
      exact_mod_cast hp
  have hν : 0 ≤ nuR r m n := (nuR_pos hr hm hn).le
  have hω : ∀ j s, 0 ≤ prefixWeight r j s := fun j s => (prefixWeight_le hr j s).1
  have hsA := summable_weighted (hω i) (summable_weight_pow hr (prefixWeight_le hr i) (n - 1)) _
    fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  have hsB := summable_weighted (hω (i + m))
    (summable_weight_pow hr (prefixWeight_le hr (i + m)) (n - 1)) _
    fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  have hsT : ∀ u : ℕ, Summable fun t : ℕ => prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)| :=
    fun u => summable_weighted (hω m) (summable_weight_pow hr (prefixWeight_le hr m) (n - 1)) _
      fun t => abs_eval_add_le hpn u t
  have hF : ∀ u t : ℕ, 0 ≤ prefixWeight r i u * (prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)|) :=
    fun u t => mul_nonneg (hω i u) (mul_nonneg (hω m t) (abs_nonneg _))
  rw [← ENNReal.ofReal_le_ofReal_iff (prefA_nonneg hr (i + m) p)]
  calc ENNReal.ofReal (nuR r m n * prefA r i p)
      = ∑' u : ℕ, ENNReal.ofReal (nuR r m n * (prefixWeight r i u * |p.eval (u : ℝ)|)) := by
        rw [prefA, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg
          (fun u => mul_nonneg hν (mul_nonneg (hω i u) (abs_nonneg _))) (hsA.mul_left _)]
    _ ≤ ∑' u : ℕ, ENNReal.ofReal (∑' t : ℕ,
          prefixWeight r i u * (prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)|)) :=
        ENNReal.tsum_le_tsum fun u => ENNReal.ofReal_le_ofReal (by
          rw [tsum_mul_left, mul_left_comm]
          exact mul_le_mul_of_nonneg_left (nuR_mul_le_shift hr m hp u) (hω i u))
    _ = ∑' u : ℕ, ∑' t : ℕ, ENNReal.ofReal
          (prefixWeight r i u * (prefixWeight r m t * |p.eval ((u + t : ℕ) : ℝ)|)) :=
        tsum_congr fun u => ENNReal.ofReal_tsum_of_nonneg (hF u) ((hsT u).mul_left _)
    _ = ∑' x : ℕ × ℕ, ENNReal.ofReal
          (prefixWeight r i x.1 * (prefixWeight r m x.2 * |p.eval ((x.1 + x.2 : ℕ) : ℝ)|)) :=
        (ENNReal.tsum_prod' (f := fun x : ℕ × ℕ => ENNReal.ofReal
          (prefixWeight r i x.1 * (prefixWeight r m x.2 * |p.eval ((x.1 + x.2 : ℕ) : ℝ)|)))).symm
    _ = ∑' σ : (Σ s : ℕ, Finset.antidiagonal s), ENNReal.ofReal (prefixWeight r i σ.2.1.1 *
          (prefixWeight r m σ.2.1.2 * |p.eval ((σ.2.1.1 + σ.2.1.2 : ℕ) : ℝ)|)) :=
        (Finset.sigmaAntidiagonalEquivProd.tsum_eq (fun x : ℕ × ℕ => ENNReal.ofReal
          (prefixWeight r i x.1 * (prefixWeight r m x.2 * |p.eval ((x.1 + x.2 : ℕ) : ℝ)|)))).symm
    _ = ∑' s : ℕ, ∑' x : Finset.antidiagonal s, ENNReal.ofReal (prefixWeight r i x.1.1 *
          (prefixWeight r m x.1.2 * |p.eval ((x.1.1 + x.1.2 : ℕ) : ℝ)|)) :=
        ENNReal.tsum_sigma' _
    _ = ∑' s : ℕ, ENNReal.ofReal (prefixWeight r (i + m) s * |p.eval (s : ℝ)|) := by
        refine tsum_congr fun s => ?_
        rw [Finset.tsum_subtype (Finset.antidiagonal s) (fun x : ℕ × ℕ => ENNReal.ofReal
          (prefixWeight r i x.1 * (prefixWeight r m x.2 * |p.eval ((x.1 + x.2 : ℕ) : ℝ)|))),
          ← ENNReal.ofReal_sum_of_nonneg fun x _ => hF x.1 x.2, prefixWeight_add r hi hm s,
          Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_antidiagonal.1 hx]
        ring
    _ = ENNReal.ofReal (prefA r (i + m) p) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun s => mul_nonneg (hω _ s) (abs_nonneg _)) hsB).symm

theorem prefixShift : PrefixShift := by
  intro r hr n i m hn hi hm
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  have hmul : ∀ j, 1 ≤ j → nuR r j n * nuR r m n ≤ nuR r (j + m) n := fun j hj =>
    le_ciInf fun p => by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left (nuR_le_prefA hr j p.2.1 p.2.2)
        (nuR_pos hr hm hn).le).trans (prefA_add_ge hr hj hm hn p.2.1)
  refine ⟨fun p hp => prefA_add_ge hr hi hm hn hp, hmul i hi, ?_⟩
  induction i, hi using Nat.le_induction with
  | base => rw [pow_one]
  | succ j hj ih =>
    rw [pow_succ]
    have h1 := (nuR_pos hr le_rfl hn).le
    have hstep : nuR r j n * nuR r 1 n ≤ nuR r (j + 1) n := by
      exact le_ciInf fun p => by
        rw [mul_comm]
        exact (mul_le_mul_of_nonneg_left (nuR_le_prefA hr j p.2.1 p.2.2) h1).trans
          (prefA_add_ge hr hj le_rfl hn p.2.1)
    exact (mul_le_mul_of_nonneg_right ih h1).trans hstep

end CoefficientMass
