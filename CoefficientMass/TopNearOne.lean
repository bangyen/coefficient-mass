/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.AllRowsTwo
import CoefficientMass.OnePolyRows

/-!
# The Top Row Near the Root 1

This module proves Lemma 6.5 of `coefficient-mass-rows.tex`: for `n ≥ 1` and `1 < r ≤ 2`,
`β_r(n) ≤ e^{4n+2} C_n (r - 1)` with `C_n = ∏_{i=1}^n (2i + 1)`.  Put `m = ⌈1/(r - 1)⌉` and
`B_j = [2jm, 2jm + m)`.  For `q ∈ Q_n` pick `s_j ∈ B_j` where `|q|` is least on `B_j`; Lagrange
interpolation at `s_1, …, s_n` (nodes `m` apart, `s_j < (2j + 1)m`) gives
`1 ≤ C_n ∑_j |q(s_j)| ≤ (C_n/m) ∑_{s ∈ B} |q(s)|`, and `r^{-s} ≥ e^{-4n-2}` on `B`.  (The paper
averages over all choices of the `s_j`; the least values give the same bound.)

## Definitions

* `cN`.
* `block`.
* `TopNearOne`.

## Theorems

* `cN_pos`.
* `block_sep`.
* `abs_basis_zero_le`.
* `one_le_rpow_mul_exp`.
* `m_le_rowPhi`.
* `topNearOne`.
-/

open Polynomial

namespace CoefficientMass

/-- `C_n = ∏_{i=1}^n (2i + 1)`. -/
noncomputable def cN (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (2 * (i : ℝ) + 1)

/-- `B_j = [2jm, 2jm + m)`. -/
def block (m j : ℕ) : Finset ℕ :=
  Finset.Ico (2 * j * m) (2 * j * m + m)

/-- Lemma 6.5 of `coefficient-mass-rows.tex`: for `n ≥ 1` and `1 < r ≤ 2`,
`β_r(n) ≤ e^{4n+2} C_n (r - 1)`; in particular `β_r(n) ≤ 1` (so Theorem 6.4 applies) when
`r - 1 ≤ e^{-4n-2}/C_n`. -/
def TopNearOne : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 1 < r → r ≤ 2 →
    rowValue r n 1 ≤ Real.exp (4 * n + 2) * cN n * (r - 1) ∧
    (r - 1 ≤ Real.exp (-(4 * n + 2)) / cN n → rowValue r n 1 ≤ 1)

theorem cN_pos (n : ℕ) : 0 < cN n := Finset.prod_pos fun i _ => by positivity

/-- Points of `B_i` lie more than `m` below points of `B_j` for `i < j`. -/
theorem block_sep {m i j x y : ℕ} (hij : i < j) (hx : x ∈ block m i) (hy : y ∈ block m j) :
    x + m < y := by
  rw [block, Finset.mem_Ico] at hx hy
  have : 2 * i * m + 2 * m ≤ 2 * j * m := by nlinarith
  omega

/-- `|ℓ_j(0)| ≤ C_n` for the Lagrange basis at points `s_i ∈ B_i`. -/
theorem abs_basis_zero_le {n m : ℕ} (hm : 1 ≤ m) {x : ℕ → ℕ}
    (hx : ∀ j ∈ Finset.Icc 1 n, x j ∈ block m j) {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    |(Lagrange.basis (Finset.Icc 1 n) (fun i => (x i : ℝ)) j).eval 0| ≤ cN n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Lagrange.basis, eval_prod, Finset.abs_prod, cN, ← Finset.mul_prod_erase _ _ hj]
  have hj1 : (1 : ℝ) ≤ 2 * (j : ℝ) + 1 := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  refine le_trans ?_ (le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity) hj1)
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => ?_
  obtain ⟨hij, hi⟩ := Finset.mem_erase.1 hi
  rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, zero_sub, abs_mul,
    abs_inv, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (x i)), inv_mul_eq_div]
  have hxi := hx i hi
  have hxj := hx j hj
  have hsep : (m : ℝ) ≤ |(x j : ℝ) - x i| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have := block_sep h hxi hxj
      rw [abs_of_pos (sub_pos.2 (by exact_mod_cast (show x i < x j by omega)))]
      have : ((x i + m : ℕ) : ℝ) < x j := by exact_mod_cast this
      push_cast at this
      linarith
    · have := block_sep h hxj hxi
      rw [abs_of_neg (sub_neg.2 (by exact_mod_cast (show x j < x i by omega)))]
      have : ((x j + m : ℕ) : ℝ) < x i := by exact_mod_cast this
      push_cast at this
      linarith
  rw [div_le_iff₀ (hm'.trans_le hsep)]
  rw [block, Finset.mem_Ico] at hxi
  have hlt : (x i : ℝ) < 2 * i * m + m := by exact_mod_cast hxi.2
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-- `1 ≤ e^{4n+2} r^{-s}` for `s ≤ (2n + 1)m`, `m = ⌈1/(r - 1)⌉`, `1 < r ≤ 2`. -/
theorem one_le_rpow_mul_exp {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (n : ℕ) {s : ℕ}
    (hs : s ≤ (2 * n + 1) * ⌈1 / (r - 1)⌉₊) : 1 ≤ Real.exp (4 * n + 2) * (1 / r) ^ s := by
  have hr1 : 0 < r - 1 := by linarith
  have hceil : (⌈1 / (r - 1)⌉₊ : ℝ) < 1 / (r - 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm2 : (r - 1) * ⌈1 / (r - 1)⌉₊ ≤ 2 := by
    have := mul_lt_mul_of_pos_left hceil hr1
    rw [mul_add, mul_one_div_cancel hr1.ne', mul_one] at this
    linarith
  have hs' : (r - 1) * s ≤ 4 * n + 2 := by
    have : (s : ℝ) ≤ (2 * n + 1) * ⌈1 / (r - 1)⌉₊ := by exact_mod_cast hs
    nlinarith [mul_le_mul_of_nonneg_left this hr1.le,
      mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ 2 * n + 1)]
  have hrs : r ^ s ≤ Real.exp (4 * n + 2) := by
    calc r ^ s ≤ Real.exp (r - 1) ^ s :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (r - 1)]) s
      _ = Real.exp (s * (r - 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (4 * n + 2) := Real.exp_le_exp.2 (by linarith)
  rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
  exact hrs

/-- `m ≤ C_n e^{4n+2} Φ_r(q)` for `q ∈ Q_n`, `m = ⌈1/(r - 1)⌉`. -/
theorem m_le_rowPhi {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n)
    (hq0 : q.eval 0 = 1) :
    (⌈1 / (r - 1)⌉₊ : ℝ) ≤ cN n * Real.exp (4 * n + 2) * rowPhi r q := by
  classical
  set m := ⌈1 / (r - 1)⌉₊
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 fun h => by
    have : 1 / (r - 1) ≤ (m : ℝ) := Nat.le_ceil _
    rw [h, Nat.cast_zero] at this
    have : 0 < 1 / (r - 1) := one_div_pos.2 (by linarith)
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : ∀ j, (block m j).Nonempty := fun j =>
    ⟨2 * j * m, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  choose x hx hmin using fun j => (block m j).exists_min_image (fun s => |q.eval (s : ℝ)|) (hne j)
  -- Lagrange interpolation at the chosen points
  have hinj : Set.InjOn (fun i => (x i : ℝ)) (Finset.Icc 1 n : Set ℕ) := fun i _ j _ h => by
    by_contra hij
    have h'' : (x i : ℝ) = x j := h
    have h' : x i = x j := by exact_mod_cast h''
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have := block_sep hlt (hx i) (hx j)
      omega
    · have := block_sep hlt (hx j) (hx i)
      omega
  have hlag := abs_eval_le_lagrange hinj (by rwa [Nat.card_Icc, Nat.add_sub_cancel]) 0
  rw [hq0, abs_one] at hlag
  have h1 : 1 ≤ cN n * ∑ j ∈ Finset.Icc 1 n, |q.eval (x j : ℝ)| := by
    refine hlag.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_basis_zero_le hm (fun j _ => hx j) hj) (abs_nonneg _)
  -- the least value on a block is at most its average
  have havg : ∀ j, (m : ℝ) * |q.eval (x j : ℝ)| ≤ ∑ s ∈ block m j, |q.eval (s : ℝ)| := fun j => by
    have := Finset.card_nsmul_le_sum (block m j) (fun s => |q.eval (s : ℝ)|) _ (hmin j)
    rwa [block, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul] at this
  -- the blocks lie in `[1, (2n + 1)m]`
  have hsub : ∀ j ∈ Finset.Icc 1 n, block m j ⊆ Finset.Icc 1 ((2 * n + 1) * m) :=
    fun j hj s hs => by
      rw [block, Finset.mem_Ico] at hs
      obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
      have h2 : 2 * m ≤ 2 * j * m := by nlinarith
      have h3 : 2 * j * m ≤ 2 * n * m := by nlinarith
      have h4 : (2 * n + 1) * m = 2 * n * m + m := by ring
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 n : Set ℕ) (block m) :=
    fun i _ j _ hij => Finset.disjoint_left.2 fun s hsi hsj => by
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have := block_sep hlt hsi hsj
        omega
      · have := block_sep hlt hsj hsi
        omega
  have hw : ∀ s ∈ Finset.Icc 1 ((2 * n + 1) * m), |q.eval (s : ℝ)| ≤
      Real.exp (4 * n + 2) * (|q.eval (s : ℝ)| * (1 / r) ^ s) := fun s hs => by
    have := one_le_rpow_mul_exp hr hr2 n (Finset.mem_Icc.1 hs).2
    nlinarith [abs_nonneg (q.eval (s : ℝ))]
  have hΦ : ∑ s ∈ (Finset.Icc 1 n).biUnion (block m), |q.eval (s : ℝ)| ≤
      Real.exp (4 * n + 2) * rowPhi r q := by
    have hU : (Finset.Icc 1 n).biUnion (block m) ⊆ Finset.Icc 1 ((2 * n + 1) * m) :=
      Finset.biUnion_subset.2 hsub
    calc ∑ s ∈ (Finset.Icc 1 n).biUnion (block m), |q.eval (s : ℝ)|
        ≤ ∑ s ∈ Finset.Icc 1 ((2 * n + 1) * m), |q.eval (s : ℝ)| :=
          Finset.sum_le_sum_of_subset_of_nonneg hU fun _ _ _ => abs_nonneg _
      _ ≤ ∑ s ∈ Finset.Icc 1 ((2 * n + 1) * m),
            Real.exp (4 * n + 2) * (|q.eval (s : ℝ)| * (1 / r) ^ s) :=
          Finset.sum_le_sum hw
      _ = Real.exp (4 * n + 2) * phiD r ((2 * n + 1) * m) q := by rw [phiD, Finset.mul_sum]
      _ ≤ Real.exp (4 * n + 2) * rowPhi r q := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [← sum_range_eq_phiD]
          exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_rowPhi hr q)
  rw [Finset.sum_biUnion hdisj] at hΦ
  have hsum : (m : ℝ) * ∑ j ∈ Finset.Icc 1 n, |q.eval (x j : ℝ)| ≤
      ∑ j ∈ Finset.Icc 1 n, ∑ s ∈ block m j, |q.eval (s : ℝ)| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => havg j
  have hC := cN_pos n
  calc (m : ℝ) = m * 1 := (mul_one _).symm
    _ ≤ m * (cN n * ∑ j ∈ Finset.Icc 1 n, |q.eval (x j : ℝ)|) :=
        mul_le_mul_of_nonneg_left h1 hm'.le
    _ = cN n * (m * ∑ j ∈ Finset.Icc 1 n, |q.eval (x j : ℝ)|) := by ring
    _ ≤ cN n * (Real.exp (4 * n + 2) * rowPhi r q) :=
        mul_le_mul_of_nonneg_left (hsum.trans hΦ) hC.le
    _ = cN n * Real.exp (4 * n + 2) * rowPhi r q := by ring

theorem topNearOne : TopNearOne := by
  intro n hn r hr hr2
  have hr1 : 0 < r - 1 := by linarith
  have hC := cN_pos n
  have hE := Real.exp_pos (4 * n + 2)
  haveI : Nonempty {q : ℝ[X] // q.degree < n ∧ q.eval 0 = 1 ∧
      ∀ s ∈ (∅ : Finset ℕ), q.eval (s : ℝ) = 0} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one, fun s hs => absurd hs
      (Finset.notMem_empty s)⟩⟩
  -- `μ_r(∅, n) ≥ 1/((r - 1) C_n e^{4n+2})`
  have hμ : 1 / (Real.exp (4 * n + 2) * cN n * (r - 1)) ≤ muR r ∅ n := le_ciInf fun q => by
    have hm := m_le_rowPhi hr hr2 q.2.1 q.2.2.1
    have hceil : 1 / (r - 1) ≤ (⌈1 / (r - 1)⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ (mul_pos (mul_pos hE hC) hr1)]
    have := hceil.trans hm
    rw [div_le_iff₀ hr1] at this
    nlinarith
  have hβ : rowValue r n 1 ≤ Real.exp (4 * n + 2) * cN n * (r - 1) := by
    rw [(rowValueDual r hr).2 n hn]
    have := one_div_le_one_div_of_le (one_div_pos.2 (mul_pos (mul_pos hE hC) hr1)) hμ
    rwa [one_div_one_div] at this
  refine ⟨hβ, fun hsmall => hβ.trans ?_⟩
  rw [le_div_iff₀ hC] at hsmall
  have : Real.exp (4 * n + 2) * Real.exp (-(4 * n + 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [mul_le_mul_of_nonneg_left hsmall hE.le]

end CoefficientMass
