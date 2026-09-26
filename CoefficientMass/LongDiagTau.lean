/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarPrefix
import CoefficientMass.NbNodes

/-!
# A Lower Bound for `τ_k(n)`

This module proves the lower bound for `τ_k(n)` in Proposition 6.8(a) of
`coefficient-mass-rows.tex`.  Past the mode, `w_k(s)/ω_k(s) = 1 - (k - 1)/(s - k + 1) > 2 - r`.
Lagrange interpolation at `t_l = M + l` has `|ℓ_l(0)| ≤ 2^{n-1} binom(M + n - 1, n - 1)` for
`M ≥ 1`, so for `M > (k - 1)r/(r - 1)`, `p ∈ Q_n` and `r ≤ 2`,
`(2 - r) ω_k(M) ≤ r^{n-1} 2^{n-1} binom(M + n - 1, n - 1) ∑_{s ≥ 2k-2} w_k(s) |p(s)|`.

## Theorems

* `prod_range_add_one_eq`.
* `abs_basis_nodes_le_choose`.
* `wDiff_ge`.
* `tauR_ge`.
-/

open Polynomial

namespace CoefficientMass

/-- `∏_{j < m} (M + 1 + j) = m! binom(M + m, m)`. -/
theorem prod_range_add_one_eq (M m : ℕ) :
    ∏ j ∈ Finset.range m, ((M : ℝ) + 1 + j) = (m.factorial : ℝ) * ((M + m).choose m : ℝ) := by
  induction m with
  | zero => rw [Finset.prod_range_zero, Nat.factorial_zero, Nat.choose_zero_right]; norm_num
  | succ m ih =>
    have e : (M + m + 1) * (M + m).choose m = (M + m + 1).choose (m + 1) * (m + 1) :=
      Nat.add_one_mul_choose_eq (M + m) m
    have e' : ((M : ℝ) + m + 1) * ((M + m).choose m : ℝ) =
        ((M + m + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast e
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, ← add_assoc M m 1]
    push_cast
    linear_combination (m.factorial : ℝ) * e'

/-- `|ℓ_l(0)| ≤ 2^{n-1} binom(M + n - 1, n - 1)` at the nodes `M, …, M + n - 1`, `M ≥ 1`. -/
theorem abs_basis_nodes_le_choose {M : ℕ} (hM : 1 ≤ M) {n l : ℕ} (hl : l ∈ Finset.range n) :
    |(Lagrange.basis (Finset.range n) (fun j => ((M + j : ℕ) : ℝ)) l).eval 0| ≤
      2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ) := by
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
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ((M + (n - 1)).choose (n - 1) : ℝ) := ⟨_, rfl⟩
  rw [← hCdef]
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- `∏_{j ≠ l} (M + j) ≤ (n - 1)! C`
  have hfull : (∏ j ∈ Finset.range n, ((M : ℝ) + j)) = M * ((n - 1).factorial * C) := by
    rw [hCdef]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.prod_range_succ', Nat.add_sub_cancel, ← prod_range_add_one_eq M m]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by ring
  have hE0 : 0 ≤ ∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j) :=
    Finset.prod_nonneg fun j _ => by positivity
  have hnum : ∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j) ≤ (n - 1).factorial * C := by
    have h := Finset.prod_erase_mul (Finset.range n) (fun j => (M : ℝ) + j) hl
    rw [hfull] at h
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    refine le_of_mul_le_mul_left (?_ : (M : ℝ) * _ ≤ M * _) (by linarith)
    nlinarith
  have hbin := Nat.choose_mul_factorial_mul_factorial (show l ≤ n - 1 by omega)
  have hbin' : ((n - 1).choose l : ℝ) * (l.factorial * (n - 1 - l).factorial) =
      (n - 1).factorial := by rw [← mul_assoc]; exact_mod_cast hbin
  have hf2 : (0 : ℝ) < (l.factorial : ℝ) * (n - 1 - l).factorial :=
    mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) (Nat.cast_pos.2 (Nat.factorial_pos _))
  have h2 : ((n - 1).choose l : ℝ) ≤ 2 ^ (n - 1) := by exact_mod_cast Nat.choose_le_two_pow _ _
  have hC : 0 ≤ C := by rw [hCdef]; exact Nat.cast_nonneg _
  rw [div_le_iff₀ hf2]
  calc ∏ j ∈ (Finset.range n).erase l, ((M : ℝ) + j) ≤ (n - 1).factorial * C := hnum
    _ = ((n - 1).choose l : ℝ) * C * (l.factorial * (n - 1 - l).factorial) := by
        rw [← hbin']
        ring
    _ ≤ 2 ^ (n - 1) * C * (l.factorial * (n - 1 - l).factorial) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hC) hf2.le

/-- `w_k(t) ≥ (2 - r) ω_k(t)` for `k ≥ 2` and `t > (k - 1)r/(r - 1)`. -/
theorem wDiff_ge {r : ℝ} (hr : 1 < r) {k t : ℕ} (hk : 2 ≤ k)
    (ht : ((k : ℝ) - 1) * r / (r - 1) < t) : (2 - r) * prefixWeight r k t ≤ wDiff r k t := by
  have hr1 : 0 < r - 1 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have ht' : ((k : ℝ) - 1) * r < t * (r - 1) := by rwa [div_lt_iff₀ hr1] at ht
  have hkt : k ≤ t := by
    have : ((k : ℝ) - 1) * 1 ≤ ((k : ℝ) - 1) * r := mul_le_mul_of_nonneg_left hr.le (by linarith)
    have : (k : ℝ) < t + 1 := by nlinarith
    have : k < t + 1 := by exact_mod_cast this
    omega
  have h := Nat.choose_succ_right_eq (t - 1) (k - 2)
  rw [show k - 2 + 1 = k - 1 by omega] at h
  have hc : ((t - 1 - (k - 2) : ℕ) : ℝ) = t - k + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc2 : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : ((t - 1).choose (k - 1) : ℝ) * ((k : ℝ) - 1) =
      ((t - 1).choose (k - 2) : ℝ) * ((t : ℝ) - k + 1) := by
    rw [← hc, ← hc2]
    exact_mod_cast h
  unfold wDiff prefixWeight
  rw [if_pos (by omega), if_pos (by omega), show k - 1 - 1 = k - 2 by omega]
  have hx : 0 < (1 / r) ^ t := by positivity
  have hC0 : (0 : ℝ) ≤ ((t - 1).choose (k - 1) : ℝ) := Nat.cast_nonneg _
  -- `binom(t - 1, k - 2) ≤ (r - 1) binom(t - 1, k - 1)`
  have htk : (0 : ℝ) < (t : ℝ) - k + 1 := by
    have : (k : ℝ) ≤ t := by exact_mod_cast hkt
    linarith
  have hkey : ((t - 1).choose (k - 2) : ℝ) ≤ (r - 1) * ((t - 1).choose (k - 1) : ℝ) := by
    refine le_of_mul_le_mul_right (?_ : _ * ((t : ℝ) - k + 1) ≤ _ * ((t : ℝ) - k + 1)) htk
    rw [← h']
    have : (k : ℝ) - 1 ≤ (r - 1) * ((t : ℝ) - k + 1) := by nlinarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hkey hx.le]

/-- `τ_k(n) ≥ (2 - r) ω_k(M)/(r^{n-1} 2^{n-1} binom(M + n - 1, n - 1))` for `1 < r ≤ 2`, `k ≥ 2`
and `M > (k - 1)r/(r - 1)`. -/
theorem tauR_ge {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) {M : ℕ}
    (hM : ((k : ℝ) - 1) * r / (r - 1) < M) :
    (2 - r) * prefixWeight r k M /
      (r ^ (n - 1) * (2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ))) ≤ tauR r k n := by
  have hr1 : 0 < r - 1 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hX : 2 * ((k : ℝ) - 1) ≤ ((k : ℝ) - 1) * r / (r - 1) := by
    rw [le_div_iff₀ hr1]
    nlinarith
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast this
  have hM2 : 2 * k - 2 ≤ M := by
    have : ((2 * k - 2 : ℕ) : ℝ) < M := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact_mod_cast this.le
  have hB : 0 < r ^ (n - 1) * (2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ)) :=
    mul_pos (by positivity) (mul_pos (by positivity)
      (Nat.cast_pos.2 (Nat.choose_pos (by omega))))
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  unfold tauR
  refine le_ciInf fun p => ?_
  obtain ⟨q, hq, hq0⟩ := p
  have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  have hpn : q.natDegree < n := by
    rw [degree_eq_natDegree hqne] at hq
    exact_mod_cast hq
  have hsum : ∀ j, Summable fun s : ℕ => prefixWeight r j s * |q.eval (s : ℝ)| := fun j =>
    summable_weighted (fun s => (prefixWeight_le hr j s).1)
      (summable_weight_pow hr (prefixWeight_le hr j) (n - 1)) _
      fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  have hwsum : Summable fun j : ℕ =>
      wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)| :=
    ((summable_nat_add_iff (2 * k - 2)).2 ((hsum k).sub (hsum (k - 1)))).congr fun j => by
      simp only [wDiff]
      ring
  have hinj : Set.InjOn (fun j => ((M + j : ℕ) : ℝ)) (Finset.range n : Set ℕ) :=
    fun i _ j _ h => by
      have h'' : ((M + i : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) := h
      have h' : M + i = M + j := by exact_mod_cast h''
      omega
  have hlag := abs_eval_le_lagrange hinj (by rwa [Finset.card_range]) 0
  rw [hq0, abs_one] at hlag
  set S := ∑ l ∈ Finset.range n, |q.eval ((M + l : ℕ) : ℝ)|
  have hC : 0 ≤ 2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ) := by positivity
  set C := 2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ)
  have h1 : 1 ≤ C * S := by
    refine hlag.trans ?_
    rw [mul_comm, Finset.sum_mul]
    exact Finset.sum_le_sum fun l hl =>
      mul_le_mul_of_nonneg_left (abs_basis_nodes_le_choose hM1 hl) (abs_nonneg _)
  have hstep : ∀ l ∈ Finset.range n,
      (2 - r) * prefixWeight r k M ≤ r ^ (n - 1) * wDiff r k (M + l) := fun l hl => by
    have hl' := Finset.mem_range.1 hl
    have hrk : 0 < (r - 1) ^ k := pow_pos hr1 k
    have h := nbLaw_le_add hr k M l
    unfold nbLaw at h
    have hωl : prefixWeight r k M ≤ r ^ l * prefixWeight r k (M + l) := by
      refine le_of_mul_le_mul_left (?_ : (r - 1) ^ k * _ ≤ (r - 1) ^ k * _) hrk
      linarith
    have hpow : r ^ l ≤ r ^ (n - 1) := pow_le_pow_right₀ hr.le (by omega)
    have hω0 := (prefixWeight_le hr k (M + l)).1
    have hw := wDiff_ge hr hk (t := M + l) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) l])
    have h2r : 0 ≤ 2 - r := by linarith
    calc (2 - r) * prefixWeight r k M ≤ (2 - r) * (r ^ (n - 1) * prefixWeight r k (M + l)) :=
          mul_le_mul_of_nonneg_left (hωl.trans (mul_le_mul_of_nonneg_right hpow hω0)) h2r
      _ = r ^ (n - 1) * ((2 - r) * prefixWeight r k (M + l)) := by ring
      _ ≤ r ^ (n - 1) * wDiff r k (M + l) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
  have hre : ∑ l ∈ Finset.range n, wDiff r k (M + l) * |q.eval ((M + l : ℕ) : ℝ)| =
      ∑ j ∈ Finset.Ico (M - (2 * k - 2)) (M - (2 * k - 2) + n),
        wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)| := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun l _ => by
      rw [show M - (2 * k - 2) + l + (2 * k - 2) = M + l by omega]
  have hT : ∑ l ∈ Finset.range n, wDiff r k (M + l) * |q.eval ((M + l : ℕ) : ℝ)| ≤
      ∑' j : ℕ, wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)| := by
    rw [hre]
    exact hwsum.sum_le_tsum _ fun j _ =>
      mul_nonneg (wDiff_nonneg r hr hk (by omega)) (abs_nonneg _)
  have h2 : (2 - r) * prefixWeight r k M * S ≤ r ^ (n - 1) *
      ∑' j : ℕ, wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)| := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hT (by positivity))
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hstep l hl) (abs_nonneg _)
  have hA : 0 ≤ (2 - r) * prefixWeight r k M :=
    mul_nonneg (by linarith) (prefixWeight_le hr k M).1
  rw [div_le_iff₀ hB]
  calc (2 - r) * prefixWeight r k M = (2 - r) * prefixWeight r k M * 1 := (mul_one _).symm
    _ ≤ (2 - r) * prefixWeight r k M * (C * S) := mul_le_mul_of_nonneg_left h1 hA
    _ = C * ((2 - r) * prefixWeight r k M * S) := by ring
    _ ≤ C * (r ^ (n - 1) *
          ∑' j : ℕ, wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)|) :=
        mul_le_mul_of_nonneg_left h2 hC
    _ = (∑' j : ℕ, wDiff r k (j + (2 * k - 2)) * |q.eval ((j + (2 * k - 2) : ℕ) : ℝ)|) *
          (r ^ (n - 1) * C) := by ring

end CoefficientMass
