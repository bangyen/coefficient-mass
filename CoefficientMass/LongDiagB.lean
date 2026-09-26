/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LongDiagA

/-!
# Propagating the Explicit Condition

This module proves Proposition 6.8(b) of `coefficient-mass-rows.tex`.  With
`d = ⌈r/(r - 1)⌉`, `M_{k+1} - M_k ≤ d`, each step of the binomial gains at most
`1 + (n - 1)/(M_k + 1)`, and `4√((k + 1)r)/(r - 1) + 1 ≤ √(1 + 1/k)(4√(kr)/(r - 1) + 1)`; so
`Ξ(k + 1) ≤ γ_k Ξ(k)` with `γ_k = θ(1 + (n - 1)/(M_k + 1))^d √(1 + 1/k)` nonincreasing.

## Definitions

* `dR`.
* `gammaK`.

## Theorems

* `mK_succ_le`.
* `mK_le_succ`.
* `choose_succ_le`.
* `choose_add_le`.
* `sK_succ_le`.
* `xiK_nonneg`.
* `xiK_succ_le`.
* `gammaK_succ_le`.
* `xiK_le_of_ge`.
-/

namespace CoefficientMass

/-- `d = ⌈r/(r - 1)⌉`. -/
noncomputable def dR (r : ℝ) : ℕ :=
  ⌈r / (r - 1)⌉₊

/-- `γ_k = θ (1 + (n - 1)/(M_k + 1))^d √(1 + 1/k)`. -/
noncomputable def gammaK (r : ℝ) (n k : ℕ) : ℝ :=
  4 * (r - 1) / r ^ 2 * (1 + ((n : ℝ) - 1) / ((mK r k : ℝ) + 1)) ^ dR r *
    Real.sqrt (1 + 1 / (k : ℝ))

theorem mK_succ_le {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) :
    mK r (k + 1) ≤ mK r k + dR r := by
  have hr1 : 0 < r - 1 := by linarith
  have hk' : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have ha : 0 ≤ ((k : ℝ) - 1) * r / (r - 1) := div_nonneg (mul_nonneg hk' (by linarith)) hr1.le
  have hb : 0 ≤ r / (r - 1) := div_nonneg (by linarith) hr1.le
  have e : (((k + 1 : ℕ) : ℝ) - 1) * r / (r - 1) = ((k : ℝ) - 1) * r / (r - 1) + r / (r - 1) := by
    push_cast
    ring
  unfold mK dR
  rw [e]
  suffices h : ⌊((k : ℝ) - 1) * r / (r - 1) + r / (r - 1)⌋₊ <
      ⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + ⌈r / (r - 1)⌉₊ + 1 by omega
  rw [Nat.floor_lt (add_nonneg ha hb)]
  push_cast
  linarith [Nat.lt_floor_add_one (((k : ℝ) - 1) * r / (r - 1)), Nat.le_ceil (r / (r - 1))]

theorem mK_le_succ {r : ℝ} (hr : 1 < r) (k : ℕ) : mK r k ≤ mK r (k + 1) := by
  have hr1 : 0 < r - 1 := by linarith
  unfold mK
  refine Nat.add_le_add_right (Nat.floor_le_floor ?_) 1
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hr1.le
  push_cast
  linarith

/-- `binom(m + a + 1, a) ≤ binom(m + a, a) (1 + a/(M + 1))` for `M ≤ m`. -/
theorem choose_succ_le {a m M : ℕ} (hm : M ≤ m) :
    ((m + a + 1).choose a : ℝ) ≤ ((m + a).choose a : ℝ) * (1 + (a : ℝ) / ((M : ℝ) + 1)) := by
  have h := Nat.choose_mul_succ_eq (m + a) a
  rw [show m + a + 1 - a = m + 1 by omega] at h
  have h' : ((m + a).choose a : ℝ) * ((m : ℝ) + a + 1) =
      ((m + a + 1).choose a : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast h
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hmM : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hC : (0 : ℝ) ≤ ((m + a).choose a : ℝ) := Nat.cast_nonneg _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hq : (a : ℝ) ≤ a / ((M : ℝ) + 1) * ((m : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hM1]
    nlinarith
  refine le_of_mul_le_mul_right (?_ : _ * ((m : ℝ) + 1) ≤ _ * ((m : ℝ) + 1)) hm1
  rw [← h']
  nlinarith [mul_le_mul_of_nonneg_left hq hC]

/-- `binom(M' + a, a) ≤ binom(M + a, a) (1 + a/(M + 1))^{M' - M}` for `M ≤ M'`. -/
theorem choose_add_le {a M M' : ℕ} (h : M ≤ M') :
    ((M' + a).choose a : ℝ) ≤
      ((M + a).choose a : ℝ) * (1 + (a : ℝ) / ((M : ℝ) + 1)) ^ (M' - M) := by
  induction M', h using Nat.le_induction with
  | base => rw [Nat.sub_self, pow_zero, mul_one]
  | succ m hm ih =>
    have hq : (0 : ℝ) ≤ 1 + (a : ℝ) / ((M : ℝ) + 1) := by positivity
    rw [show m + 1 + a = m + a + 1 by ring, show m + 1 - M = m - M + 1 by omega, pow_succ]
    calc ((m + a + 1).choose a : ℝ) ≤ ((m + a).choose a : ℝ) * (1 + (a : ℝ) / ((M : ℝ) + 1)) :=
          choose_succ_le hm
      _ ≤ ((M + a).choose a : ℝ) * (1 + (a : ℝ) / ((M : ℝ) + 1)) ^ (m - M) *
            (1 + (a : ℝ) / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_right ih hq
      _ = _ := by ring

/-- `4√((k + 1)r)/(r - 1) + 1 ≤ √(1 + 1/k) (4√(kr)/(r - 1) + 1)`. -/
theorem sK_succ_le {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) :
    4 * Real.sqrt (((k + 1 : ℕ) : ℝ) * r) / (r - 1) + 1 ≤
      Real.sqrt (1 + 1 / (k : ℝ)) * (4 * Real.sqrt (k * r) / (r - 1) + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e : Real.sqrt (1 + 1 / (k : ℝ)) * Real.sqrt (k * r) = Real.sqrt (((k + 1 : ℕ) : ℝ) * r) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  have h1 : 1 ≤ Real.sqrt (1 + 1 / (k : ℝ)) := Real.one_le_sqrt.2 (by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith)
  rw [← e]
  have e2 : 4 * (Real.sqrt (1 + 1 / (k : ℝ)) * Real.sqrt (k * r)) / (r - 1) =
      Real.sqrt (1 + 1 / (k : ℝ)) * (4 * Real.sqrt (k * r) / (r - 1)) := by ring
  rw [e2, mul_add, mul_one]
  linarith

theorem xiK_nonneg {r : ℝ} (hr : 1 < r) (n k : ℕ) : 0 ≤ xiK r n k := by
  have hr1 : 0 < r - 1 := by linarith
  unfold xiK
  refine mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg (by linarith)
    (by positivity)) _) (by positivity)) (Nat.cast_nonneg _)) ?_
  have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg (k * r))) hr1.le
  linarith

/-- `Ξ(k + 1) ≤ γ_k Ξ(k)`. -/
theorem xiK_succ_le {r : ℝ} (hr : 1 < r) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    xiK r n (k + 1) ≤ gammaK r n k * xiK r n k := by
  have hr1 : 0 < r - 1 := by linarith
  have hθ : 0 ≤ 4 * (r - 1) / r ^ 2 := div_nonneg (by linarith) (by positivity)
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn, Nat.cast_one]
  have hq : (1 : ℝ) ≤ 1 + ((n - 1 : ℕ) : ℝ) / ((mK r k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / ((mK r k : ℝ) + 1) := by positivity
    linarith
  have hC : (((mK r (k + 1)) + (n - 1)).choose (n - 1) : ℝ) ≤
      ((mK r k + (n - 1)).choose (n - 1) : ℝ) *
        (1 + ((n - 1 : ℕ) : ℝ) / ((mK r k : ℝ) + 1)) ^ dR r :=
    (choose_add_le (mK_le_succ hr k)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hq (by have := mK_succ_le hr hk; omega)) (Nat.cast_nonneg _))
  have hS := sK_succ_le hr hk
  have hs0 : 0 ≤ 4 * Real.sqrt (((k + 1 : ℕ) : ℝ) * r) / (r - 1) + 1 := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (Real.sqrt_nonneg (((k + 1 : ℕ) : ℝ) * r))) hr1.le
    linarith
  have hA : 0 ≤ (4 * (r - 1) / r ^ 2) ^ k * (4 * (r - 1) / r ^ 2) * (2 * r) ^ (n - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hθ k) hθ) (by positivity)
  unfold xiK gammaK
  rw [show mK r (k + 1) + n - 1 = mK r (k + 1) + (n - 1) by omega,
    show mK r k + n - 1 = mK r k + (n - 1) by omega, hcast, pow_succ]
  calc (4 * (r - 1) / r ^ 2) ^ k * (4 * (r - 1) / r ^ 2) * (2 * r) ^ (n - 1) *
        (((mK r (k + 1)) + (n - 1)).choose (n - 1) : ℝ) *
        (4 * Real.sqrt (((k + 1 : ℕ) : ℝ) * r) / (r - 1) + 1)
      ≤ (4 * (r - 1) / r ^ 2) ^ k * (4 * (r - 1) / r ^ 2) * (2 * r) ^ (n - 1) *
          (((mK r k + (n - 1)).choose (n - 1) : ℝ) *
            (1 + ((n - 1 : ℕ) : ℝ) / ((mK r k : ℝ) + 1)) ^ dR r) *
          (Real.sqrt (1 + 1 / (k : ℝ)) * (4 * Real.sqrt (k * r) / (r - 1) + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC hA) hS hs0
          (mul_nonneg hA (mul_nonneg (Nat.cast_nonneg _) (by positivity)))
    _ = _ := by ring

/-- `γ_{k+1} ≤ γ_k`. -/
theorem gammaK_succ_le {r : ℝ} (hr : 1 < r) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    gammaK r n (k + 1) ≤ gammaK r n k := by
  have hθ : 0 ≤ 4 * (r - 1) / r ^ 2 := div_nonneg (by linarith) (by positivity)
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hM : ((mK r k : ℕ) : ℝ) ≤ ((mK r (k + 1) : ℕ) : ℝ) := by exact_mod_cast mK_le_succ hr k
  have hq : 1 + ((n : ℝ) - 1) / ((mK r (k + 1) : ℝ) + 1) ≤
      1 + ((n : ℝ) - 1) / ((mK r k : ℝ) + 1) :=
    add_le_add_left (div_le_div_of_nonneg_left hn1 (by positivity) (by linarith)) 1
  have hq0 : 0 ≤ 1 + ((n : ℝ) - 1) / ((mK r (k + 1) : ℝ) + 1) := by positivity
  have hsq : Real.sqrt (1 + 1 / ((k + 1 : ℕ) : ℝ)) ≤ Real.sqrt (1 + 1 / (k : ℝ)) :=
    Real.sqrt_le_sqrt (add_le_add_left (one_div_le_one_div_of_le hk0 (by push_cast; linarith)) 1)
  unfold gammaK
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) hθ) hsq
    (Real.sqrt_nonneg _) (mul_nonneg hθ (pow_nonneg (by positivity) _))

/-- Proposition 6.8(b) of `coefficient-mass-rows.tex`: if `γ_{k_1} ≤ 1`, then `Ξ(k) ≤ Ξ(k_1)`
and `γ_k ≤ 1` for every `k ≥ k_1`. -/
theorem xiK_le_of_ge {r : ℝ} (hr : 1 < r) {n k₁ : ℕ} (hn : 1 ≤ n) (hk₁ : 1 ≤ k₁)
    (hγ : gammaK r n k₁ ≤ 1) : ∀ k, k₁ ≤ k → xiK r n k ≤ xiK r n k₁ ∧ gammaK r n k ≤ 1 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨le_rfl, hγ⟩
  | succ k hk ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, (gammaK_succ_le hr hn (by omega)).trans h2⟩
    calc xiK r n (k + 1) ≤ gammaK r n k * xiK r n k := xiK_succ_le hr hn (by omega)
      _ ≤ 1 * xiK r n k := mul_le_mul_of_nonneg_right h2 (xiK_nonneg hr n k)
      _ = xiK r n k := one_mul _
      _ ≤ xiK r n k₁ := h1

end CoefficientMass
