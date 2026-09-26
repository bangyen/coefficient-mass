/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowFarFactor
import CoefficientMass.RowValueDual

/-!
# Every Row Is at Most a Top Row

This module proves the second claim of Proposition 2.1(c) of `coefficient-mass-rows.tex`:
`V_r(L, k) ≤ β_r(n)` with `n = L - k + 1`.  Exempt the far block `S_N = [N + 1, N + k - 1]`.
An admissible `q` factors as `q = r_{S_N} q_0` with `deg q_0 < n` and `q_0(0) = 1`, and
`r_{S_N} ≥ (1 - M/N)^{k - 1}` on `[1, M]`, so
`μ_r(S_N, L) ≥ (1 - M/N)^{k - 1} (μ_r(∅, n) - ε)` once `M` is large; Bernoulli's inequality
and Proposition 2.1(b) finish the proof.

## Definitions

* `RowValueTop`.

## Theorems

* `muR_far_ge`.
* `rowValue_le_top`.
* `rowValueTop`.
-/

open Polynomial

namespace CoefficientMass

/-- Proposition 2.1(c) of `coefficient-mass-rows.tex`, second claim: for `r > 1` and
`1 ≤ k ≤ L`, `V_r(L, k) ≤ β_r(L - k + 1)`. -/
def RowValueTop : Prop :=
  ∀ r : ℝ, 1 < r → ∀ L k : ℕ, 1 ≤ k → k ≤ L → rowValue r L k ≤ rowValue r (L - k + 1) 1

/-- `μ_r([N + 1, N + m], n + m) ≥ (1 - M/N)^m c` when `Φ_{r,M} ≥ c` on the admissible
polynomials of `μ_r(∅, n)`. -/
theorem muR_far_ge {r : ℝ} (hr : 1 < r) {n m N M : ℕ} (hn : 1 ≤ n) (hN : 0 < N) (hMN : M ≤ N)
    {c : ℝ} (hc : ∀ q₀ : ℝ[X], q₀.degree < n → q₀.eval 0 = 1 →
      c ≤ ∑ d ∈ Finset.range M, |q₀.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) :
    (1 - (M : ℝ) / N) ^ m * c ≤ muR r (Finset.Icc (N + 1) (N + m)) (n + m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase : 0 ≤ 1 - (M : ℝ) / N := by
    rw [sub_nonneg, div_le_one hN']
    exact_mod_cast hMN
  have h0 : 0 ∉ Finset.Icc (N + 1) (N + m) := fun h => by
    have := (Finset.mem_Icc.1 h).1
    omega
  have hcard : (Finset.Icc (N + 1) (N + m)).card < n + m := by rw [Nat.card_Icc]; omega
  haveI : Nonempty {q : ℝ[X] // q.degree < ↑(n + m) ∧ q.eval 0 = 1 ∧
      ∀ s ∈ Finset.Icc (N + 1) (N + m), q.eval (s : ℝ) = 0} :=
    ⟨⟨_, confPolyP_admissible h0 hcard⟩⟩
  refine le_ciInf fun q => ?_
  obtain ⟨q, hq, hq0, hqS⟩ := q
  obtain ⟨q₀, hdeg, h00, hfac⟩ := factor_far hq hq0 hqS
  have hq₀ : q₀.degree < n :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (show q₀.natDegree < n by omega))
  calc (1 - (M : ℝ) / N) ^ m * c
      ≤ (1 - (M : ℝ) / N) ^ m *
          ∑ d ∈ Finset.range M, |q₀.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left (hc q₀ hq₀ h00) (pow_nonneg hbase _)
    _ ≤ ∑ d ∈ Finset.range M, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun d hd => ?_
        have hdM : d + 1 ≤ M := Finset.mem_range.1 hd
        have hπ := confPolyP_far_ge (m := m) hN hdM hMN
        rw [hfac, abs_mul, abs_of_nonneg ((pow_nonneg hbase _).trans hπ), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hπ (abs_nonneg _))
          (by positivity)
    _ ≤ rowPhi r q := sum_le_rowPhi hr q M

/-- `V_r(L, k) ≤ 1/μ_r(∅, L - k + 1)`. -/
theorem rowValue_le_top {r : ℝ} (hr : 1 < r) {L k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) :
    rowValue r L k ≤ 1 / muR r ∅ (L - k + 1) := by
  set n := L - k + 1
  set μ := muR r ∅ n
  have hμ : 0 < μ := muR_pos hr (Finset.notMem_empty 0) (by rw [Finset.card_empty]; omega)
  have key : ∀ ε, 0 < ε → ε < 1 → ε < μ → rowValue r L k ≤ 1 / ((1 - ε) * (μ - ε)) := by
    intro ε hε hε1 hεμ
    obtain ⟨M₀, hM₀⟩ := exists_trunc_ge hr ∅ n hε
    set M := max n M₀
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (((k - 1 : ℕ) : ℝ) * M / ε)
    set N := max N₀ (M + 1)
    have hMN : M ≤ N := (Nat.le_succ M).trans (le_max_right _ _)
    have hN : 0 < N := lt_of_lt_of_le (Nat.succ_pos M) (le_max_right _ _)
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hc := muR_far_ge hr (m := k - 1) (by omega : 1 ≤ n) hN hMN (c := μ - ε)
      fun q₀ hq₀ h00 => hM₀ M (le_max_right _ _) q₀ hq₀ h00 fun s hs => absurd hs
        (Finset.notMem_empty s)
    -- Bernoulli: `(1 - M/N)^{k - 1} ≥ 1 - ε`
    have hbern : 1 - ε ≤ (1 - (M : ℝ) / N) ^ (k - 1) := by
      have hMN' : (M : ℝ) / N ≤ 1 := by
        rw [div_le_one hN']
        exact_mod_cast hMN
      have hMN0 : 0 ≤ (M : ℝ) / N := div_nonneg (Nat.cast_nonneg M) hN'.le
      have h := one_add_mul_le_pow (a := -((M : ℝ) / N)) (by linarith) (k - 1)
      rw [← sub_eq_add_neg] at h
      have hsmall : ((k - 1 : ℕ) : ℝ) * ((M : ℝ) / N) ≤ ε := by
        have hN₀' : ((k - 1 : ℕ) : ℝ) * M / ε < N :=
          hN₀.trans_le (by exact_mod_cast le_max_left _ _)
        rw [div_lt_iff₀ hε] at hN₀'
        rw [← mul_div_assoc, div_le_iff₀ hN']
        linarith
      linarith
    have hS0 : 0 ∉ Finset.Icc (N + 1) (N + (k - 1)) := fun h => by
      have := (Finset.mem_Icc.1 h).1
      omega
    have hSc : (Finset.Icc (N + 1) (N + (k - 1))).card + 1 = k := by rw [Nat.card_Icc]; omega
    have hLnm : n + (k - 1) = L := by omega
    rw [hLnm] at hc
    have hlow : (1 - ε) * (μ - ε) ≤ muR r (Finset.Icc (N + 1) (N + (k - 1))) L :=
      (mul_le_mul_of_nonneg_right hbern (by linarith)).trans hc
    exact (rowValue_le_inv hr hk hkL hS0 hSc).trans
      (one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith)) hlow)
  by_contra hlt
  push_neg at hlt
  set V := rowValue r L k
  set W := (1 / μ + V) / 2 with hWdef
  have hW : 1 / μ < W := by linarith
  have hWV : W < V := by linarith
  have hW0 : 0 < W := lt_trans (by positivity) hW
  have hWμ : 1 / W < μ := by
    rw [div_lt_iff₀ hW0]
    rw [div_lt_iff₀ hμ] at hW
    linarith
  set ε := (μ - 1 / W) / (2 * (1 + μ)) with hεdef
  have hW1 : 0 < 1 / W := by positivity
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεμ' : ε * (2 * (1 + μ)) = μ - 1 / W := div_mul_cancel₀ _ (by positivity)
  have hε1 : ε < 1 := by
    rw [hεdef, div_lt_one (by positivity)]
    linarith
  have hεμ : ε < μ := by
    rw [hεdef, div_lt_iff₀ (by positivity)]
    nlinarith
  have hprod : 1 / W < (1 - ε) * (μ - ε) := by nlinarith [sq_nonneg ε]
  have hbound := key ε hε hε1 hεμ
  have : 1 / ((1 - ε) * (μ - ε)) < W := by
    rw [div_lt_iff₀ (mul_pos (by linarith) (by linarith))]
    rw [div_lt_iff₀ hW0] at hprod
    linarith
  linarith

theorem rowValueTop : RowValueTop := fun r hr L k hk hkL => by
  rw [(rowValueDual r hr).2 _ (by omega)]
  exact rowValue_le_top hr hk hkL

end CoefficientMass
