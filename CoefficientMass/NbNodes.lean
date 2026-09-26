/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.NbMode

/-!
# Interpolating at the Mode

This module proves the lower bound for `m_k(n) = ν_k(n)/a^k` in Lemma 3.4 of
`coefficient-mass-rows.tex`.  Lagrange interpolation at `M, …, M + n - 1` gives
`|ℓ_l(0)| ≤ (2(M + n - 1))^{n-1}/(n - 1)!`, so `∑_l |p(M + l)| ≥ (n - 1)!/(2(M + n - 1))^{n-1}`
for `p ∈ Q_n`, and `P(M + l) ≥ r^{-(n-1)} P(M)` gives
`(r - 1)^k A_k(p) ≥ (n - 1)! P(M)/(r^{n-1} (2(M + n - 1))^{n-1})`.

## Theorems

* `prod_erase_abs_sub`.
* `abs_basis_nodes_le`.
* `nbLaw_nodes_le`.
-/

open Polynomial

namespace CoefficientMass

/-- `∏_{j < n, j ≠ l} |l - j| = l! (n - 1 - l)!`. -/
theorem prod_erase_abs_sub {n l : ℕ} (hl : l < n) :
    ∏ j ∈ (Finset.range n).erase l, |(l : ℝ) - j| = (l.factorial : ℝ) * (n - 1 - l).factorial := by
  have hl' : l + 1 ≤ n := hl
  induction n, hl' using Nat.le_induction with
  | base =>
    rw [Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self,
      show l + 1 - 1 - l = 0 by omega, Nat.factorial_zero, Nat.cast_one, mul_one]
    clear hl
    induction l with
    | zero => rw [Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one]
    | succ l ih =>
      rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul,
        Finset.prod_congr rfl fun j _ => by
          rw [Nat.cast_succ, Nat.cast_succ, add_sub_add_right_eq_sub],
        ih, Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      ring
  | succ n hn ih =>
    rw [Finset.range_add_one, Finset.erase_insert_of_ne (show n ≠ l by omega),
      Finset.prod_insert fun h => Finset.notMem_range_self (Finset.mem_of_mem_erase h),
      ih (by omega), show n + 1 - 1 - l = n - 1 - l + 1 by omega, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast (show l ≤ n by omega)))]
    have : ((n - 1 - l : ℕ) : ℝ) + 1 = n - l := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      ring
    rw [this]
    ring

/-- `|ℓ_l(0)| ≤ (2(M + n - 1))^{n-1}/(n - 1)!` for the Lagrange basis at `M, …, M + n - 1`. -/
theorem abs_basis_nodes_le (M : ℕ) {n l : ℕ} (hl : l ∈ Finset.range n) :
    |(Lagrange.basis (Finset.range n) (fun j => ((M + j : ℕ) : ℝ)) l).eval 0| ≤
      (2 * ((M : ℝ) + n - 1)) ^ (n - 1) / (n - 1).factorial := by
  have hl' := Finset.mem_range.1 hl
  have hfac : ∀ j ∈ (Finset.range n).erase l,
      |(Lagrange.basisDivisor ((M + l : ℕ) : ℝ) ((M + j : ℕ) : ℝ)).eval 0| =
        ((M : ℝ) + j) / |(l : ℝ) - j| := fun j _ => by
    rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, zero_sub, abs_mul,
      abs_inv, abs_neg, inv_mul_eq_div]
    push_cast
    rw [abs_of_nonneg (by positivity), add_sub_add_left_eq_sub]
  rw [Lagrange.basis, eval_prod, Finset.abs_prod, Finset.prod_congr rfl hfac,
    Finset.prod_div_distrib, prod_erase_abs_sub hl']
  have hX : 0 ≤ (M : ℝ) + n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith [Nat.cast_nonneg (α := ℝ) M]
  have hnum : ∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j) ≤ ((M : ℝ) + n - 1) ^ (n - 1) := by
    calc ∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j)
        ≤ ∏ _j ∈ (Finset.range n).erase l, ((M : ℝ) + n - 1) :=
          Finset.prod_le_prod (fun j _ => by positivity) fun j hj => by
            have := Finset.mem_range.1 (Finset.mem_of_mem_erase hj)
            have : (j : ℝ) + 1 ≤ n := by exact_mod_cast this
            linarith
      _ = ((M : ℝ) + n - 1) ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem hl, Finset.card_range]
  have hfn : ((n - 1).factorial : ℝ) ≤ 2 ^ (n - 1) * (l.factorial * (n - 1 - l).factorial) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show l ≤ n - 1 by omega)
    have : (n - 1).factorial ≤ 2 ^ (n - 1) * (l.factorial * (n - 1 - l).factorial) := by
      rw [← h, mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    exact_mod_cast this
  have hf1 : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hf2 : (0 : ℝ) < (l.factorial : ℝ) * (n - 1 - l).factorial :=
    mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) (Nat.cast_pos.2 (Nat.factorial_pos _))
  rw [div_le_div_iff₀ hf2 hf1, mul_pow]
  calc (∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j)) * (n - 1).factorial
      ≤ ((M : ℝ) + n - 1) ^ (n - 1) * (2 ^ (n - 1) * (l.factorial * (n - 1 - l).factorial)) :=
        mul_le_mul hnum hfn hf1.le (pow_nonneg hX _)
    _ = 2 ^ (n - 1) * ((M : ℝ) + n - 1) ^ (n - 1) * (l.factorial * (n - 1 - l).factorial) := by
        ring

/-- `(r - 1)^k ν_k(n) ≥ (n - 1)! P(M)/(r^{n-1} (2(M + n - 1))^{n-1})` for every `M`. -/
theorem nbLaw_nodes_le {r : ℝ} (hr : 1 < r) {k n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    (n - 1).factorial * nbLaw r k M / (r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1)) ≤
      (r - 1) ^ k * nuR r k n := by
  have hpow : 0 < (2 * ((M : ℝ) + n - 1)) ^ (n - 1) := by
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]
      norm_num
    · have : (2 : ℝ) ≤ n := by exact_mod_cast h
      exact pow_pos (by linarith [Nat.cast_nonneg (α := ℝ) M]) _
  have hf1 : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hrk : 0 < (r - 1) ^ k := pow_pos (by linarith) k
  have hrn : 0 < r ^ (n - 1) := by positivity
  have hP0 := nbLaw_nonneg hr k M
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  rw [← div_le_iff₀' hrk, nuR, wInf]
  refine le_ciInf fun p => ?_
  obtain ⟨q, hq, hq0⟩ := p
  rw [div_le_iff₀' hrk, div_le_iff₀ (mul_pos hrn hpow)]
  have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  have hpn : q.natDegree < n := by
    rw [degree_eq_natDegree hqne] at hq
    exact_mod_cast hq
  have hsum : Summable fun s : ℕ => prefixWeight r k s * |q.eval (s : ℝ)| :=
    summable_weighted (fun s => (prefixWeight_le hr k s).1)
      (summable_weight_pow hr (prefixWeight_le hr k) (n - 1)) _
      fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  have hinj : Set.InjOn (fun j => ((M + j : ℕ) : ℝ)) (Finset.range n : Set ℕ) :=
    fun i _ j _ h => by
      have h'' : ((M + i : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) := h
      have h' : M + i = M + j := by exact_mod_cast h''
      omega
  have hlag := abs_eval_le_lagrange hinj (by rwa [Finset.card_range]) 0
  rw [hq0, abs_one] at hlag
  set S := ∑ l ∈ Finset.range n, |q.eval ((M + l : ℕ) : ℝ)|
  have h12 : ((n - 1).factorial : ℝ) ≤ S * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) := by
    have h2 : 1 ≤ S * ((2 * ((M : ℝ) + n - 1)) ^ (n - 1) / (n - 1).factorial) := by
      refine hlag.trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun l hl =>
        mul_le_mul_of_nonneg_left (abs_basis_nodes_le M hl) (abs_nonneg _)
    rw [mul_div_assoc', le_div_iff₀ hf1, one_mul] at h2
    exact h2
  have h3 : nbLaw r k M * S ≤
      r ^ (n - 1) * ∑ l ∈ Finset.range n, nbLaw r k (M + l) * |q.eval ((M + l : ℕ) : ℝ)| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ((nbLaw_le_add hr k M l).trans ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hr.le (by have := Finset.mem_range.1 hl; omega)) (nbLaw_nonneg hr k _)
  have h4 : ∑ l ∈ Finset.range n, nbLaw r k (M + l) * |q.eval ((M + l : ℕ) : ℝ)| ≤
      (r - 1) ^ k * ∑' s : ℕ, prefixWeight r k s * |q.eval (s : ℝ)| := by
    have : ∑ l ∈ Finset.range n, nbLaw r k (M + l) * |q.eval ((M + l : ℕ) : ℝ)| =
        (r - 1) ^ k * ∑ s ∈ Finset.Ico M (M + n), prefixWeight r k s * |q.eval (s : ℝ)| := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [nbLaw, mul_assoc]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun s _ =>
      mul_nonneg (prefixWeight_le hr k s).1 (abs_nonneg _)) hrk.le
  calc ((n - 1).factorial : ℝ) * nbLaw r k M
      ≤ nbLaw r k M * (S * (2 * ((M : ℝ) + n - 1)) ^ (n - 1)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h12 hP0
    _ = nbLaw r k M * S * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) := by ring
    _ ≤ r ^ (n - 1) * ((r - 1) ^ k * ∑' s : ℕ, prefixWeight r k s * |q.eval (s : ℝ)|) *
          (2 * ((M : ℝ) + n - 1)) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (h3.trans (mul_le_mul_of_nonneg_left h4 hrn.le)) hpow.le
    _ = (r - 1) ^ k * (∑' s : ℕ, prefixWeight r k s * |q.eval (s : ℝ)|) *
          (r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1)) := by ring

end CoefficientMass
