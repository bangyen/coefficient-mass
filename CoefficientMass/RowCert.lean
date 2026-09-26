/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDefs

/-!
# The Certificate for a Row

This module proves Lemma 4.5 of `coefficient-mass.tex`.  A multiple of
`(x - 2)^L` is annihilated by `∑_j f_j q(j) 2^j` for every polynomial `q` of
degree below `L` (`sum_coeff_mul_eval_eq_zero`), the operator form
`ψ(D - θ) F (2) = 0` of the paper; with `q(j) = r_Z(D - j)` this is the
dual identity, and the large positions it leaves out bound `b_k`.

## Theorems

* `degree_forwardDiff_lt`.
* `sum_coeff_mul_eval_eq_zero`.
* `confPoly_eq_eval`.
* `summable_confTail`.
* `rowCertificate`.
* `everyRow_of_star`.
-/

open Polynomial

namespace CoefficientMass

/-- The forward difference `q(x + 1) - q(x)` lowers the degree. -/
theorem degree_forwardDiff_lt {q : ℝ[X]} (hq : q ≠ 0) (hdeg : 0 < q.natDegree) :
    (q.comp (X + 1) - q).degree < q.degree := by
  have h1 : (X + 1 : ℝ[X]).natDegree = 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X]
  have hlc : (X + 1 : ℝ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, h1, coeff_add, coeff_X_one, coeff_one]
    norm_num
  have hcomp : (q.comp (X + 1)).natDegree = q.natDegree := by
    rw [natDegree_comp, h1, mul_one]
  have hne : q.comp (X + 1) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hcomp
    omega
  refine degree_sub_lt ?_ hne ?_ |>.trans_eq ?_
  · rw [degree_eq_natDegree hne, degree_eq_natDegree hq, hcomp]
  · rw [leadingCoeff_comp (by rw [h1]; norm_num), hlc, one_pow, mul_one]
  · rw [degree_eq_natDegree hne, degree_eq_natDegree hq, hcomp]

/-- One factor `x - 2`: the sum against `q` becomes the sum against
`2 (q(x + 1) - q(x))`. -/
theorem sum_mul_X_sub_two (H : ℝ[X]) (q : ℝ[X]) {N : ℕ} (hN : H.natDegree < N) :
    ∑ j ∈ Finset.range (N + 1), (H * (X - C 2)).coeff j * q.eval (j : ℝ) * 2 ^ j =
      ∑ j ∈ Finset.range N,
        H.coeff j * (C 2 * (q.comp (X + 1) - q)).eval (j : ℝ) * 2 ^ j := by
  have hHN : H.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hN
  rw [Finset.sum_range_succ']
  simp only [coeff_mul_X_sub_C, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
    eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_C]
  have hsplit : ∀ j : ℕ,
      (H.coeff j - H.coeff (j + 1) * 2) * q.eval ((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1) =
        H.coeff j * q.eval ((j : ℝ) + 1) * 2 ^ (j + 1) -
          H.coeff (j + 1) * q.eval ((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1 + 1) := by
    intro j
    push_cast
    ring
  simp only [hsplit, Finset.sum_sub_distrib]
  have htel : ∑ j ∈ Finset.range N, H.coeff (j + 1) * q.eval ((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1 + 1) +
      H.coeff 0 * q.eval ((0 : ℕ) : ℝ) * 2 ^ 1 =
        ∑ j ∈ Finset.range N, H.coeff j * q.eval (j : ℝ) * 2 ^ (j + 1) := by
    rw [← Finset.sum_range_succ' (fun j => H.coeff j * q.eval (j : ℝ) * 2 ^ (j + 1)),
      Finset.sum_range_succ, hHN, zero_mul, zero_mul, add_zero]
  have hsum : ∑ j ∈ Finset.range N,
      H.coeff j * (2 * (q.eval ((j : ℝ) + 1) - q.eval (j : ℝ))) * 2 ^ j =
        ∑ j ∈ Finset.range N, H.coeff j * q.eval ((j : ℝ) + 1) * 2 ^ (j + 1) -
          ∑ j ∈ Finset.range N, H.coeff j * q.eval (j : ℝ) * 2 ^ (j + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, ← htel]
  simp only [Nat.cast_zero, pow_one]
  ring

/-- The operator identity `ψ(D - θ) F (2) = 0`: a multiple of `(x - 2)^L`
is annihilated by `∑_j f_j q(j) 2^j` whenever `deg q < L`. -/
theorem sum_coeff_mul_eval_eq_zero (L : ℕ) :
    ∀ (G q : ℝ[X]) (N : ℕ), q.degree < L → (G * (X - C 2) ^ L).natDegree < N →
      ∑ j ∈ Finset.range N, (G * (X - C 2) ^ L).coeff j * q.eval (j : ℝ) * 2 ^ j = 0 := by
  induction L with
  | zero =>
    intro G q N hq _
    have : q = 0 := by
      by_contra h
      rw [Nat.cast_zero] at hq
      exact absurd hq (not_lt.2 (zero_le_degree_iff.2 h))
    rw [this]
    simp only [eval_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  | succ L ih =>
    intro G q N hq hN
    by_cases hG : G = 0
    · rw [hG, zero_mul]
      simp only [coeff_zero, zero_mul, Finset.sum_const_zero]
    set H := G * (X - C 2) ^ L with hH
    have hF : G * (X - C 2) ^ (L + 1) = H * (X - C 2) := by rw [hH, pow_succ, mul_assoc]
    have hHne : H ≠ 0 := mul_ne_zero hG (pow_ne_zero _ (X_sub_C_ne_zero 2))
    have hdegF : (H * (X - C 2)).natDegree = H.natDegree + 1 := by
      rw [natDegree_mul hHne (X_sub_C_ne_zero 2), natDegree_X_sub_C]
    rw [hF] at hN ⊢
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_mul_X_sub_two H q (by omega)]
    by_cases hq0 : q = 0
    · rw [hq0]
      simp only [zero_comp, sub_zero, mul_zero, eval_zero, zero_mul, Finset.sum_const_zero]
    by_cases hqd : q.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hqd, C_comp, sub_self, mul_zero]
      simp only [eval_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    refine ih G _ M ?_ (show H.natDegree < M by omega)
    have hlt := degree_forwardDiff_lt hq0 (Nat.pos_of_ne_zero hqd)
    have hqL : q.degree ≤ L := by
      rw [degree_eq_natDegree hq0] at hq ⊢
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hq)
    rw [degree_C_mul (by norm_num : (2 : ℝ) ≠ 0)]
    exact lt_of_lt_of_le hlt hqL

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
  have hg : ∀ i, Summable fun d : ℕ => |p.coeff i| * (((d + 1 : ℕ) : ℝ) ^ i * (1 / 2 : ℝ) ^ (d + 1)) :=
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

/-- The partial sums of `Φ(Z)`. -/
theorem sum_le_confTail (Z : Finset ℕ) (D : ℕ) :
    ∑ d ∈ Finset.range D, |confPoly Z (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) ≤ confTail Z :=
  sum_le_tsum _ (fun _ _ => by positivity) (summable_confTail Z)

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
    exact_mod_cast (by omega : q.natDegree < L)
  obtain ⟨G, hG⟩ := hdvd
  have hFG : G * (X - C 2) ^ L = F := by rw [hG, mul_comm]
  have hψ0 : ψ.eval 0 = 1 := by
    rw [confPolyP, eval_prod]
    exact Finset.prod_eq_one fun z _ => by rw [eval_add, eval_mul, eval_C, eval_C, eval_X]; ring
  have hsum0 := sum_coeff_mul_eval_eq_zero L G q (D + 1) hqdeg (by rw [hFG]; omega)
  rw [hFG, Finset.sum_range_succ, hq, sub_self, hψ0,
    show F.coeff D = 1 from hF.coeff_natDegree] at hsum0
  have hsum : ∑ j ∈ Finset.range D, F.coeff j * q.eval (j : ℝ) * 2 ^ j + 2 ^ D = 0 := by
    linarith
  -- the positions whose certificate value is nonzero
  set T := (Finset.range D).filter fun j => ψ.eval ((D : ℝ) - j) ≠ 0
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
    exact absurd hsum (by positivity)
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
