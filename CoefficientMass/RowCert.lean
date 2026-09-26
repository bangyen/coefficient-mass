/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowAnnihilate
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The Certificate for a Row

This module proves Lemma 4.5 of `coefficient-mass.tex`.  With
`q(j) = r_Z(D - j)` the annihilation identity is the dual identity
`∑_j f_j r_Z(D - j) 2^{j - D} = 0`; the positions it does not exempt carry
weight at most `Φ(Z)`, which bounds `b_k`.  Theorem 4.13 follows from `(∗_n)`.

## Definitions

* `confPolyP`.

## Theorems

* `confPoly_eq_eval`.
* `natDegree_confPolyP`.
* `confPolyP_eval_mem`.
* `abs_eval_le`.
* `summable_confTail`.
* `sum_le_confTail`.
* `sum_reflect`.
* `rowCertificate`.
* `everyRow_of_star`.
-/

open Polynomial

namespace CoefficientMass

/-- `r_Z` as a polynomial. -/
noncomputable def confPolyP (Z : Finset ℕ) : ℝ[X] :=
  ∏ z ∈ Z, (C (-(1 / (z : ℝ))) * X + C 1)

theorem confPoly_eq_eval (Z : Finset ℕ) (x : ℕ) : confPoly Z x = (confPolyP Z).eval (x : ℝ) := by
  rw [confPoly, confPolyP, eval_prod]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [eval_add, eval_mul, eval_C, eval_C, eval_X]
  ring

theorem natDegree_confPolyP (Z : Finset ℕ) : (confPolyP Z).natDegree ≤ Z.card := by
  refine (natDegree_prod_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun z _ => natDegree_linear_le

theorem confPolyP_eval_mem {Z : Finset ℕ} {z : ℕ} (hz : z ∈ Z) (h0 : z ≠ 0) :
    (confPolyP Z).eval (z : ℝ) = 0 := by
  rw [← confPoly_eq_eval, confPoly]
  refine Finset.prod_eq_zero hz ?_
  rw [div_self (by exact_mod_cast h0), sub_self]

theorem abs_eval_le (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * x ^ i := by
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hx i)]

theorem summable_confTail (Z : Finset ℕ) :
    Summable fun d : ℕ => |confPoly Z (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) := by
  set p := confPolyP Z
  have hg : ∀ i, Summable fun d : ℕ =>
      |p.coeff i| * (((d + 1 : ℕ) : ℝ) ^ i * (1 / 2 : ℝ) ^ (d + 1)) :=
    fun i => ((summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one i
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))).mul_left _
  refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    (summable_sum fun i (_ : i ∈ Finset.range (p.natDegree + 1)) => hg i)
  calc |confPoly Z (d + 1)| * (1 / 2 : ℝ) ^ (d + 1)
      = |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / 2 : ℝ) ^ (d + 1) := by rw [confPoly_eq_eval]
    _ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * ((d + 1 : ℕ) : ℝ) ^ i) *
          (1 / 2 : ℝ) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right (abs_eval_le p (by positivity)) (by positivity)
    _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The finite sums below `Φ(Z)`. -/
theorem sum_le_confTail (Z : Finset ℕ) (D : ℕ) :
    ∑ d ∈ Finset.range D, |confPoly Z (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) ≤ confTail Z :=
  (summable_confTail Z).sum_le_tsum _ fun _ _ => by positivity

/-- The reflection `s = D - j` of the dual identity. -/
theorem sum_reflect (ψ : ℝ[X]) (D : ℕ) :
    ∑ j ∈ Finset.range D, |ψ.eval ((D : ℝ) - j)| * 2 ^ j =
      2 ^ D * ∑ d ∈ Finset.range D, |ψ.eval ((d + 1 : ℕ) : ℝ)| * (1 / 2 : ℝ) ^ (d + 1) := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd := Finset.mem_range.1 hd
  have hc : ((D - 1 - d : ℕ) : ℝ) = D - 1 - d := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have hp : (2 : ℝ) ^ D = 2 ^ (D - 1 - d) * 2 ^ (d + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2 : ℝ) ^ (d + 1) * (1 / 2) ^ (d + 1) = 1 := by rw [← mul_pow]; norm_num
  rw [hc, show (D : ℝ) - (D - 1 - d) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, hp]
  linear_combination (-(|ψ.eval ((d + 1 : ℕ) : ℝ)| * 2 ^ (D - 1 - d))) * h1

/-- Lemma 4.5 (certificate for a row). -/
theorem rowCertificate : RowCertificate := by
  classical
  intro L k F hF hdvd hk hkL hS
  set D := F.natDegree
  set n := L - k + 1 with hn_def
  by_contra hlt
  push_neg at hlt
  set P := (Finset.range D).filter fun j => ((n : ℕ) : ℝ) ≤ ‖F.coeff j‖ with hP
  have hPc : P.card + 1 ≤ k := hlt
  set W := P.image fun j => D - j
  have hW0 : 0 ∉ W := by
    intro h
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 h
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    omega
  have hWt : W ⊆ Finset.Icc 1 (D + k) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨S, hWS, hSt, hSc⟩ := Finset.exists_subsuperset_card_eq hWt
    (Finset.card_image_le.trans (by omega : P.card ≤ k - 1))
    (by rw [Nat.card_Icc]; omega)
  have hS0 : 0 ∉ S := fun h => by
    have := Finset.mem_Icc.1 (hSt h)
    omega
  obtain ⟨Z, hSZ, hZ0, hZc, hZΦ⟩ := hS S hS0 (by omega)
  set ψ := confPolyP Z
  set q := ψ.comp (C (D : ℝ) - X)
  have hq : ∀ x : ℝ, q.eval x = ψ.eval ((D : ℝ) - x) := fun x => by
    rw [eval_comp, eval_sub, eval_C, eval_X]
  have hqdeg : q.degree < L := by
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (D : ℝ) - X).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le ((natDegree_C _).trans_le zero_le_one) natDegree_X_le)
    have := (natDegree_comp_le (p := ψ) (q := C (D : ℝ) - X)).trans
      (Nat.mul_le_mul (natDegree_confPolyP Z) h1)
    have hql : q.natDegree < L := lt_of_le_of_lt this (by omega)
    exact_mod_cast hql
  obtain ⟨G, hG⟩ := hdvd
  have hFG : G * (X - C 2) ^ L = F := by rw [hG, mul_comm]
  have hψ0 : ψ.eval 0 = 1 := by
    show (confPolyP Z).eval 0 = 1
    rw [confPolyP, eval_prod]
    exact Finset.prod_eq_one fun z _ => by rw [eval_add, eval_mul, eval_C, eval_C, eval_X]; ring
  have hsum0 := sum_coeff_mul_eval_eq_zero L G q (D + 1) hqdeg (by rw [hFG]; omega)
  rw [hFG, Finset.sum_range_succ, hq, sub_self, hψ0,
    show F.coeff D = 1 from hF.coeff_natDegree] at hsum0
  have hsum : ∑ j ∈ Finset.range D, F.coeff j * q.eval (j : ℝ) * 2 ^ j + 2 ^ D = 0 := by
    linarith
  -- the positions whose certificate value is nonzero
  set T := (Finset.range D).filter fun j : ℕ => ψ.eval ((D : ℝ) - (j : ℝ)) ≠ 0
  have hsmall : ∀ j ∈ T, ‖F.coeff j‖ < n := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    by_contra hge
    push_neg at hge
    have hjP : j ∈ P := by rw [hP, Finset.mem_filter, Finset.mem_range]; exact ⟨hj.1, hge⟩
    have hz : D - j ∈ Z := hSZ (hWS (Finset.mem_image_of_mem _ hjP))
    apply hj.2
    rw [show (D : ℝ) - j = ((D - j : ℕ) : ℝ) by rw [Nat.cast_sub hj.1.le]]
    exact confPolyP_eval_mem hz (by omega)
  have hsplit : ∑ j ∈ Finset.range D, F.coeff j * q.eval (j : ℝ) * 2 ^ j =
      ∑ j ∈ T, F.coeff j * ψ.eval ((D : ℝ) - j) * 2 ^ j := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hq]
      split_ifs with h
      · rfl
      · push_neg at h
        rw [h, mul_zero, zero_mul]
  rw [hsplit] at hsum
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    rw [hT, Finset.sum_empty, zero_add] at hsum
    exact pow_ne_zero D two_ne_zero hsum
  have hlt2 : (2 : ℝ) ^ D < n * ∑ j ∈ Finset.range D, |ψ.eval ((D : ℝ) - j)| * 2 ^ j := by
    calc (2 : ℝ) ^ D = |∑ j ∈ T, F.coeff j * ψ.eval ((D : ℝ) - j) * 2 ^ j| := by
          rw [show ∑ j ∈ T, F.coeff j * ψ.eval ((D : ℝ) - j) * 2 ^ j = -(2 : ℝ) ^ D by
            linarith, abs_neg, abs_of_pos (by positivity)]
      _ ≤ ∑ j ∈ T, ‖F.coeff j‖ * |ψ.eval ((D : ℝ) - j)| * 2 ^ j := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ j), Real.norm_eq_abs]
      _ < ∑ j ∈ T, (n : ℝ) * |ψ.eval ((D : ℝ) - j)| * 2 ^ j := by
          refine Finset.sum_lt_sum_of_nonempty hTne fun j hj => ?_
          have hne := (Finset.mem_filter.1 hj).2
          exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (hsmall j hj)
            (abs_pos.2 hne)) (by positivity)
      _ ≤ ∑ j ∈ Finset.range D, (n : ℝ) * |ψ.eval ((D : ℝ) - j)| * 2 ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = n * ∑ j ∈ Finset.range D, |ψ.eval ((D : ℝ) - j)| * 2 ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [sum_reflect] at hlt2
  have hΦ : ∑ d ∈ Finset.range D, |ψ.eval ((d + 1 : ℕ) : ℝ)| * (1 / 2 : ℝ) ^ (d + 1) ≤
      1 / n := by
    refine le_trans (le_of_eq ?_) ((sum_le_confTail Z D).trans hZΦ)
    exact Finset.sum_congr rfl fun d _ => by rw [confPoly_eq_eval]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have : (n : ℝ) * (2 ^ D * ∑ d ∈ Finset.range D,
      |ψ.eval ((d + 1 : ℕ) : ℝ)| * (1 / 2 : ℝ) ^ (d + 1)) ≤ 2 ^ D := by
    calc _ ≤ (n : ℝ) * (2 ^ D * (1 / n)) := by gcongr
      _ = 2 ^ D := by field_simp
  linarith

/-- Theorem 4.13 from `(∗_n)` for every `n ≥ 1`. -/
theorem everyRow_of_star (h : ∀ n, 1 ≤ n → Star n) : EveryRow := by
  intro L k F hF hdvd hk hkL
  refine rowCertificate L k F hF hdvd hk hkL fun S hS0 hSc => ?_
  obtain ⟨Z, hSZ, hZ0, hZc, hZΦ⟩ := h (L - k + 1) (by omega) S hS0
  exact ⟨Z, hSZ, hZ0, by omega, hZΦ⟩

end CoefficientMass
