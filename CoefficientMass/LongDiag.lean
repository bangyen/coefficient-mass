/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarPrefix
import CoefficientMass.IntZerosInf

/-!
# Long Diagonals

This module proves Theorem 6.7 of `coefficient-mass-rows.tex`.  If `N_k(r) ≤ τ_k(n)`, then for
every `ε > 0` Lemma 3.1 gives `p = r_Y` with all zeros at least `k` and
`A_k(p) ≤ ν_k(n) + ε`, and Lemma 6.6 makes `A_k(p)` the largest prefix sum; so
`ν_i(n) ≤ ν_k(n)`, `Λ_k(n) = ν_k(n)`, and Theorem 6.2 gives `V_r(L, k) = 1/ν_k(n)`.

## Definitions

* `LongDiag`.

## Theorems

* `exists_far_near_nuR`.
* `longDiag`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 6.7 of `coefficient-mass-rows.tex`: for `r > 1`, `n ≥ 1`, `k ≥ 2` and
`L = n + k - 1`, if `N_k(r) ≤ τ_k(n)` then `ν_i(n) ≤ ν_k(n)` for `1 ≤ i ≤ k` and
`V_r(L, k) = 1/ν_k(n) = min_{1 ≤ i ≤ k} 1/ν_i(n)`. -/
def LongDiag : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n k : ℕ, 1 ≤ n → 2 ≤ k → nK r k ≤ tauR r k n →
    (∀ i : ℕ, 1 ≤ i → i ≤ k → nuR r i n ≤ nuR r k n) ∧
    rowValue r (n + k - 1) k = 1 / nuR r k n ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k → 1 / nuR r k n ≤ 1 / nuR r i n

/-- Lemma 3.1 of `coefficient-mass-rows.tex` for `ω_k`: some `r_Y`, with `Y` a set of `n - 1`
integers at least `k`, has `A_k(r_Y) < ν_k(n) + ε`. -/
theorem exists_far_near_nuR {r : ℝ} (hr : 1 < r) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) : ∃ Y : Finset ℕ, (∀ y ∈ Y, k ≤ y) ∧ Y.card + 1 = n ∧
      prefA r k (confPolyP Y) < nuR r k n + ε := by
  have hvan : ∀ s, s < k → prefixWeight r k s = 0 := fun s hs => by
    unfold prefixWeight
    split_ifs with h
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    · rfl
  have hpos : ∀ s, k ≤ s → 0 < prefixWeight r k s := fun s hs => by
    rw [prefixWeight, if_pos (by omega)]
    exact mul_pos (by exact_mod_cast Nat.choose_pos (by omega)) (by positivity)
  have hν := intZerosInf (prefixWeight r k) k n hk hn hvan hpos
    (summable_weight_pow hr (prefixWeight_le hr k) (n - 1))
  haveI : Nonempty {Y : Finset ℕ // (∀ y ∈ Y, k ≤ y) ∧ Y.card + 1 = n} :=
    ⟨⟨Finset.Icc k (k + n - 2), fun y hy => (Finset.mem_Icc.1 hy).1, by
      rw [Nat.card_Icc]; omega⟩⟩
  have hlt : nuR r k n < nuR r k n + ε := by linarith
  rw [nuR, hν] at hlt
  obtain ⟨⟨Y, hYk, hYc⟩, hY⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨Y, hYk, hYc, by rw [nuR, hν]; exact hY⟩

theorem longDiag : LongDiag := by
  intro r hr n k hn hk hNτ
  have hk1 : 1 ≤ k := by omega
  -- for each `ε`, a far `r_Y` near `ν_k(n)` with `A_k` the largest prefix sum
  have hgood : ∀ ε : ℝ, 0 < ε → ∃ p : ℝ[X], p.degree < n ∧ p.eval 0 = 1 ∧
      prefA r k p < nuR r k n + ε ∧ ∀ i, 1 ≤ i → i ≤ k → prefA r i p ≤ prefA r k p :=
    fun ε hε => by
      obtain ⟨Y, hYk, hYc, hY⟩ := exists_far_near_nuR hr hk1 hn hε
      have hY0 : 0 ∉ Y := fun h => by have := hYk 0 h; omega
      obtain ⟨hdeg, hp0, -⟩ := confPolyP_admissible (L := n) hY0 (by omega)
      refine ⟨confPolyP Y, hdeg, hp0, hY, fun i hi hik => ?_⟩
      rcases hik.lt_or_eq with hik | rfl
      · have := farPrefix r hr k n hk hn Y hYc hYk i hi hik
        linarith
      · exact le_rfl
  have hνpos := nuR_pos hr hk1 hn
  have hmono : ∀ i, 1 ≤ i → i ≤ k → nuR r i n ≤ nuR r k n := fun i hi hik =>
    le_of_forall_pos_le_add fun ε hε => by
      obtain ⟨p, hp, hp0, hpk, hpi⟩ := hgood ε hε
      exact ((nuR_le_prefA hr i hp hp0).trans (hpi i hi hik)).trans hpk.le
  -- `Λ_k(n) = ν_k(n)`
  have hΛle : lambdaR r k n ≤ nuR r k n := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨p, hp, hp0, hpk, hpi⟩ := hgood ε hε
    refine (ciInf_le ⟨0, ?_⟩ (⟨p, hp, hp0⟩ : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})).trans
      (le_trans ?_ hpk.le)
    · rintro _ ⟨q, rfl⟩
      exact maxA_nonneg r k q.1
    · exact (Finset.fold_max_le _).2 ⟨prefA_nonneg hr k p, fun i hi =>
        hpi i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2⟩
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  have hΛpos : 0 < lambdaR r k n := hνpos.trans_le (le_ciInf fun p =>
    (nuR_le_prefA hr k p.2.1 p.2.2).trans (le_maxA hk1 le_rfl p.1))
  obtain ⟨-, -, hV, hmin⟩ := onePoly r hr (n + k - 1) k hk1 (by omega)
  have hL : n + k - 1 - k + 1 = n := by omega
  rw [hL] at hV hmin
  exact ⟨hmono, le_antisymm (hmin k hk1 le_rfl)
    ((one_div_le_one_div_of_le hΛpos hΛle).trans hV),
    fun i hi hik => one_div_le_one_div_of_le (nuR_pos hr hi hn) (hmono i hi hik)⟩

end CoefficientMass
