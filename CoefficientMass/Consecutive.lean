/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ExpSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Consecutive Zero Set

This module proves Lemma 2.1 of `coefficient-mass.tex`.  The generating
series `U = ∑ w_d x^d` of an exponential sum times `D = ∏ (1 - y_i x)` is the
polynomial `numer`, of degree below `c`.  When `w_1 = ⋯ = w_{c-1} = 0` and
`w_0 = 1`, this forces `numer = D - D_c x^c`, so
`U = 1 - D_c x^c ∏ 1/(1 - y_i x)`.  The product of geometric series has
nonnegative coefficients, so `(-1)^(c+1) w_d ≥ 0` for `d ≥ 1`, and the tail
is `(-1)^(c+1) ∑_{d ≥ 1} w_d`, which evaluating `numer` at `1` computes.

## Definitions

* `linFactor`.
* `geomSeries`.
* `denom`.
* `numer`.

## Theorems

* `geomSeries_mul_linFactor`.
* `coeff_prod_geomSeries_nonneg`.
* `coe_denom`.
* `expSeries_mul_denom`.
* `natDegree_denom_le`.
* `coeff_denom_card`.
* `numer_eq`.
* `consecutiveTail`.
-/

namespace CoefficientMass

/-- The linear factor `1 - t x`. -/
noncomputable def linFactor (t : ℝ) : Polynomial ℝ :=
  Polynomial.C (-t) * Polynomial.X + Polynomial.C 1

/-- The geometric series `∑ t^n x^n`. -/
noncomputable def geomSeries (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => t ^ n

/-- `∏_{j ∈ s} (1 - y_j x)`. -/
noncomputable def denom {c : ℕ} (y : Fin c → ℝ) (s : Finset (Fin c)) : Polynomial ℝ :=
  ∏ j ∈ s, linFactor (y j)

/-- `∑_i a_i ∏_{j ≠ i} (1 - y_j x)`, the generating series of the exponential
sum times `denom y univ`. -/
noncomputable def numer {c : ℕ} (a y : Fin c → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (a i) * denom y (Finset.univ.erase i)

theorem geomSeries_mul_linFactor (t : ℝ) :
    geomSeries t * (linFactor t : PowerSeries ℝ) = 1 := by
  have h : geomSeries t * (linFactor t : PowerSeries ℝ) =
      PowerSeries.C (-t) * (PowerSeries.X * geomSeries t) + geomSeries t := by
    rw [linFactor, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C,
      Polynomial.coe_X, map_one]
    ring
  ext n
  rw [h, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, geomSeries,
    PowerSeries.coeff_mk]
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, if_pos rfl, mul_zero, zero_add, pow_zero]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, if_neg n.succ_ne_zero, pow_succ]
    ring

theorem coeff_prod_geomSeries_nonneg {c : ℕ} (y : Fin c → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∀ n, 0 ≤ PowerSeries.coeff n (∏ i, geomSeries (y i)) := by
  refine Finset.prod_induction _ (fun φ => ∀ n, 0 ≤ PowerSeries.coeff n φ)
    (fun φ ψ hφ hψ n => ?_) (fun n => ?_) (fun i _ n => ?_)
  · rw [PowerSeries.coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hφ _) (hψ _)
  · rw [PowerSeries.coeff_one]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  · rw [geomSeries, PowerSeries.coeff_mk]
    exact pow_nonneg (hy i) n

theorem coe_denom {c : ℕ} (y : Fin c → ℝ) (s : Finset (Fin c)) :
    (denom y s : PowerSeries ℝ) = ∏ j ∈ s, (linFactor (y j) : PowerSeries ℝ) :=
  map_prod Polynomial.coeToPowerSeries.ringHom (fun j => linFactor (y j)) s

theorem expSeries_mul_denom {c : ℕ} (a y : Fin c → ℝ) :
    PowerSeries.mk (expSum a y) * (denom y Finset.univ : PowerSeries ℝ) =
      (numer a y : PowerSeries ℝ) := by
  have hU : PowerSeries.mk (expSum a y) = ∑ i, PowerSeries.C (a i) * geomSeries (y i) := by
    ext n
    rw [PowerSeries.coeff_mk, expSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, geomSeries, PowerSeries.coeff_mk]
  rw [hU, Finset.sum_mul, numer]
  refine (Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (map_sum Polynomial.coeToPowerSeries.ringHom _ _).symm)
  change _ = ((Polynomial.C (a i) * denom y (Finset.univ.erase i) : Polynomial ℝ) :
    PowerSeries ℝ)
  rw [Polynomial.coe_mul, Polynomial.coe_C, coe_denom, coe_denom,
    ← Finset.mul_prod_erase Finset.univ (fun j => (linFactor (y j) : PowerSeries ℝ))
      (Finset.mem_univ i),
    ← mul_assoc (PowerSeries.C (a i) * geomSeries (y i)),
    mul_assoc (PowerSeries.C (a i)), geomSeries_mul_linFactor, mul_one]

theorem natDegree_denom_le {c : ℕ} (y : Fin c → ℝ) (s : Finset (Fin c)) :
    (denom y s).natDegree ≤ s.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => Polynomial.natDegree_linear_le).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one]

theorem coeff_denom_card {c : ℕ} (y : Fin c → ℝ) (hy : ∀ i, y i ≠ 0) :
    (denom y Finset.univ).coeff c = ∏ i, -y i := by
  have hne : ∀ i ∈ Finset.univ, linFactor (y i) ≠ 0 := fun i _ h => by
    have := congrArg Polynomial.leadingCoeff h
    rw [linFactor, Polynomial.leadingCoeff_linear (neg_ne_zero.2 (hy i)),
      Polynomial.leadingCoeff_zero] at this
    exact hy i (neg_eq_zero.1 this)
  have hdeg : (denom y Finset.univ).natDegree = c := by
    rw [denom, Polynomial.natDegree_prod _ _ hne]
    simp only [linFactor, Polynomial.natDegree_linear (neg_ne_zero.2 (hy _)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hlc : (denom y Finset.univ).coeff c = (denom y Finset.univ).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hdeg]
  rw [hlc, denom, Polynomial.leadingCoeff_prod]
  exact Finset.prod_congr rfl fun i _ => Polynomial.leadingCoeff_linear (neg_ne_zero.2 (hy i))

/-- On the consecutive zero set, `numer = D - D_c x^c`. -/
theorem numer_eq {c : ℕ} (a y : Fin c → ℝ) (ha : IsCertificate a y (Finset.Ioo 0 c)) :
    numer a y = denom y Finset.univ -
      Polynomial.C ((denom y Finset.univ).coeff c) * Polynomial.X ^ c := by
  ext n
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
  rcases lt_or_ge n c with hn | hn
  · rw [if_neg hn.ne, sub_zero, ← Polynomial.coeff_coe, ← expSeries_mul_denom,
      PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [PowerSeries.coeff_mk, ha.1, one_mul, Polynomial.coeff_coe]
    · intro p hp hp0
      rw [Finset.mem_antidiagonal] at hp
      have h1 : p.1 ≠ 0 := fun h => hp0 (Prod.ext h (by omega))
      rw [PowerSeries.coeff_mk, ha.2 p.1 (Finset.mem_Ioo.2 ⟨by omega, by omega⟩), zero_mul]
    · intro h
      exact absurd (Finset.mem_antidiagonal.2 (zero_add n)) h
  · have hnum : (numer a y).coeff n = 0 := by
      rw [numer, Polynomial.finset_sum_coeff]
      refine Finset.sum_eq_zero fun i _ => Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _)
        (lt_of_le_of_lt (natDegree_denom_le y _) ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have := i.pos
      omega
    rw [hnum]
    rcases hn.lt_or_eq with hlt | heq
    · rw [if_neg hlt.ne', Polynomial.coeff_eq_zero_of_natDegree_lt, sub_zero]
      refine lt_of_le_of_lt (natDegree_denom_le y _) ?_
      rw [Finset.card_univ, Fintype.card_fin]
      exact hlt
    · subst heq
      rw [if_pos rfl, sub_self]

/-- Lemma 2.1 (consecutive zero set). -/
theorem consecutiveTail : ConsecutiveTail := by
  intro c a y _ hy0 hy1 ha
  set D := denom y Finset.univ with hD
  set Q := ∏ i, geomSeries (y i) with hQ
  have hc0 : D.coeff c = ∏ i, -y i := coeff_denom_card y fun i => (hy0 i).ne'
  have hDQ : (D : PowerSeries ℝ) * Q = 1 := by
    rw [hD, coe_denom, hQ, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by rw [mul_comm, geomSeries_mul_linFactor]
  have hU : PowerSeries.mk (expSum a y) =
      1 - PowerSeries.C (D.coeff c) * (PowerSeries.X ^ c * Q) := by
    rw [← mul_one (PowerSeries.mk (expSum a y)), ← hDQ, ← mul_assoc, expSeries_mul_denom,
      numer_eq a y ha, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, sub_mul, hDQ, mul_assoc]
  -- each tail term has the sign `(-1)^(c+1)`
  have hsign : ∀ d, 0 ≤ (-1) ^ (c + 1) * expSum a y (d + 1) := fun d => by
    have hw := congrArg (PowerSeries.coeff (d + 1)) hU
    rw [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one, if_neg d.succ_ne_zero,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', hc0, Finset.prod_neg,
      Finset.card_univ, Fintype.card_fin] at hw
    have hq : 0 ≤ ite (c ≤ d + 1) (PowerSeries.coeff (d + 1 - c) Q) 0 := by
      split_ifs
      · exact coeff_prod_geomSeries_nonneg y (fun i => (hy0 i).le) _
      · exact le_rfl
    have hsq : ((-1 : ℝ) ^ c) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hw, pow_succ]
    nlinarith [Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => (hy0 i).le,
      mul_nonneg (Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => (hy0 i).le) hq]
  have habs : ∀ d, |expSum a y (d + 1)| = (-1) ^ (c + 1) * expSum a y (d + 1) := fun d => by
    rw [← abs_of_nonneg (hsign d), abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- the untaken tail `∑_{d ≥ 1} w_d` as a finite sum of geometric series
  have hsum : HasSum (fun d => expSum a y (d + 1)) (∑ i, a i * y i * (1 - y i)⁻¹) := by
    have := hasSum_sum fun i (_ : i ∈ Finset.univ) =>
      (hasSum_geometric_of_lt_one (hy0 i).le (hy1 i)).mul_left (a i * y i)
    refine this.congr_fun fun d => ?_
    rw [expSum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ']; ring
  simp only [habs]
  convert hsum.mul_left ((-1) ^ (c + 1)) using 1
  -- evaluate `numer = D - D_c x^c` at `1`
  have hev := congrArg (Polynomial.eval 1) (numer_eq a y ha)
  have hlin : ∀ t, (linFactor t).eval 1 = 1 - t := fun t => by
    rw [linFactor, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [numer, Polynomial.eval_finset_sum, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, hc0] at hev
  simp only [Polynomial.eval_mul, Polynomial.eval_C, denom, Polynomial.eval_prod, hlin] at hev
  have hpos : ∀ i, 0 < 1 - y i := fun i => sub_pos.2 (hy1 i)
  have hP : 0 < ∏ i, (1 - y i) := Finset.prod_pos fun i _ => hpos i
  have herase : ∀ i, ∏ j ∈ Finset.univ.erase i, (1 - y j) = (∏ j, (1 - y j)) / (1 - y i) :=
    fun i => by
      rw [eq_div_iff (hpos i).ne', mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => 1 - y j) (Finset.mem_univ i)
  have h0 : ∑ i, a i = 1 := by
    have := ha.1
    rw [expSum] at this
    simpa only [pow_zero, mul_one] using this
  have hterm : ∀ i, a i * y i * (1 - y i)⁻¹ =
      a i * (∏ j ∈ Finset.univ.erase i, (1 - y j)) / (∏ j, (1 - y j)) - a i := fun i => by
    rw [herase]
    field_simp [(hpos i).ne', hP.ne']
    ring
  have hS : ∑ i, a i * y i * (1 - y i)⁻¹ = -(∏ i, -y i) / ∏ i, (1 - y i) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.sum_div, hev,
      h0, sub_div, div_self hP.ne']
    ring
  have hsq : ((-1 : ℝ) ^ c) * (-1) ^ c = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [hS, Finset.prod_neg, Finset.card_univ, Fintype.card_fin, Finset.prod_div_distrib, pow_succ]
  linear_combination (-((∏ i, y i) / ∏ i, (1 - y i))) * hsq

end CoefficientMass
