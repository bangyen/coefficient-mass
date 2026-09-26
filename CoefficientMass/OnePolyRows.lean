/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.PrefixShift

/-!
# All Rows When the Top Row Is at Most One

This module proves Theorem 6.4 of `coefficient-mass-rows.tex`.  If `β_r(n) ≤ 1`, then
`ν_1(n) = 1/β_r(n) ≥ 1`, and Lemma 6.3 with `m = 1` makes `A_i(p)` nondecreasing in `i`; so
`max_{i ≤ k} A_i(p) = A_k(p)`, `Λ_k(n) = ν_k(n)`, and Theorem 6.2 gives
`V_r(L, k) = 1/ν_k(n) = min_{i ≤ k} 1/ν_i(n)` for `L = n + k - 1`.

## Definitions

* `OnePolyRows`.

## Theorems

* `one_le_nuR_one`.
* `prefA_mono`.
* `onePolyRows`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 6.4 of `coefficient-mass-rows.tex`: for `r > 1` and `n ≥ 1` with `β_r(n) ≤ 1`,
`1 ≤ ν_1(n) ≤ ν_2(n) ≤ ⋯`, and for every `k ≥ 1` and `L = n + k - 1`,
`V_r(L, k) = 1/ν_k(n) = min_{1 ≤ i ≤ k} 1/ν_i(n)`. -/
def OnePolyRows : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n : ℕ, 1 ≤ n → rowValue r n 1 ≤ 1 →
    1 ≤ nuR r 1 n ∧ (∀ i : ℕ, 1 ≤ i → nuR r i n ≤ nuR r (i + 1) n) ∧
    ∀ k : ℕ, 1 ≤ k → rowValue r (n + k - 1) k = 1 / nuR r k n ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k → 1 / nuR r k n ≤ 1 / nuR r i n

/-- `β_r(n) ≤ 1` gives `ν_1(n) ≥ 1`. -/
theorem one_le_nuR_one {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) (hβ : rowValue r n 1 ≤ 1) :
    1 ≤ nuR r 1 n := by
  have hν := nuR_pos hr le_rfl hn
  have hem : muR r ∅ n = nuR r 1 n := by
    rw [← muR_prefix hr le_rfl hn, Nat.sub_self, add_zero,
      Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num)]
  rw [(rowValueDual r hr).2 n hn, hem] at hβ
  rwa [div_le_one hν] at hβ

/-- With `ν_1(n) ≥ 1`, `A_i(p) ≤ A_j(p)` for `1 ≤ i ≤ j` and `deg p < n`. -/
theorem prefA_mono {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) (h1 : 1 ≤ nuR r 1 n) {p : ℝ[X]}
    (hp : p.degree < n) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : prefA r i p ≤ prefA r j p := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine ih.trans ?_
    have := prefA_add_ge hr (hi.trans hij) le_rfl hn hp
    have hA := prefA_nonneg hr j p
    nlinarith

theorem onePolyRows : OnePolyRows := by
  intro r hr n hn hβ
  have h1 := one_le_nuR_one hr hn hβ
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  have hmono : ∀ i j : ℕ, 1 ≤ i → i ≤ j → nuR r i n ≤ nuR r j n := fun i j hi hij =>
    le_ciInf fun p => (nuR_le_prefA hr i p.2.1 p.2.2).trans (prefA_mono hr hn h1 p.2.1 hi hij)
  refine ⟨h1, fun i hi => hmono i (i + 1) hi (by omega), fun k hk => ?_⟩
  have hL : n + k - 1 - k + 1 = n := by omega
  obtain ⟨hp1, -, hV, hmin⟩ := onePoly r hr (n + k - 1) k hk (by omega)
  rw [hL] at hV hmin
  -- `Λ_k(n) ≤ ν_k(n)`
  have hΛ : lambdaR r k n ≤ nuR r k n := le_ciInf fun p => by
    refine (ciInf_le ⟨0, ?_⟩ p).trans ?_
    · rintro _ ⟨q, rfl⟩
      exact maxA_nonneg r k q.1
    · refine (Finset.fold_max_le _).2 ⟨prefA_nonneg hr k p.1, fun i hi => ?_⟩
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
      exact prefA_mono hr hn h1 p.2.1 hi1 hik
  refine ⟨le_antisymm (hmin k hk le_rfl) ((one_div_le_one_div_of_le ?_ hΛ).trans hV),
    fun i hi hik => one_div_le_one_div_of_le (nuR_pos hr hi hn) (hmono i k hi hik)⟩
  exact (nuR_pos hr hk hn).trans_le (le_ciInf fun p =>
    (nuR_le_prefA hr k p.2.1 p.2.2).trans (le_maxA hk le_rfl p.1))

end CoefficientMass
