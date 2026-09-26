/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LongDiag
import CoefficientMass.LongDiagB
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Long Diagonals Past a Linear Threshold

This module proves Proposition 6.8(c) of `coefficient-mass-rows.tex`.  With `m = n - 1`,
`binom(M + m, m) ≤ (e(M + m)/m)^m`, and `(1 + b/x)^x` increases in `x` (Bernoulli's
inequality); with `m ≤ k/α` and `M_k ≤ kr/(r - 1)` this gives
`Ξ(k) ≤ ρ(α)^k (4√(kr)/(r - 1) + 1)`, where `ρ(α) = θ (2re(αr/(r - 1) + 1))^{1/α}`.  When
`ρ(α) < 1` the right side is eventually below `3(2 - r)^2/r^2`.

## Definitions

* `rhoR`.

## Theorems

* `one_add_div_rpow_le`.
* `pow_choose_le`.
* `rhoR_nonneg`.
* `rhoR_pow`.
* `xiK_le_rho`.
* `exists_rho_small`.
* `longDiagC`.
-/

namespace CoefficientMass

/-- `ρ(α) = θ (2re(αr/(r - 1) + 1))^{1/α}`. -/
noncomputable def rhoR (r α : ℝ) : ℝ :=
  4 * (r - 1) / r ^ 2 * (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ (1 / α)

/-- `(1 + b/x)^x ≤ (1 + b/y)^y` for `b ≥ 0` and `0 < x ≤ y`. -/
theorem one_add_div_rpow_le {b x y : ℝ} (hb : 0 ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    (1 + b / x) ^ x ≤ (1 + b / y) ^ y := by
  have hy : 0 < y := hx.trans_le hxy
  have h := Real.one_add_mul_self_le_rpow_one_add (s := b / y)
    (by have : 0 ≤ b / y := by positivity
        linarith) (p := y / x) (by rw [le_div_iff₀ hx]; linarith)
  rw [div_mul_div_comm, mul_comm y b, mul_div_mul_right _ _ hy.ne'] at h
  calc (1 + b / x) ^ x ≤ ((1 + b / y) ^ (y / x)) ^ x := Real.rpow_le_rpow (by positivity) h hx.le
    _ = (1 + b / y) ^ y := by rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hx.ne']

/-- `c^m binom(M + m, m) ≤ (ce(1 + K/y))^y` for `c ≥ 1`, `1 ≤ m ≤ y` and `M ≤ K`. -/
theorem pow_choose_le {c K y : ℝ} (hc : 1 ≤ c) {M m : ℕ} (hm : 1 ≤ m) (hMK : (M : ℝ) ≤ K)
    (hmy : (m : ℝ) ≤ y) :
    c ^ m * ((M + m).choose m : ℝ) ≤ (c * Real.exp 1 * (1 + K / y)) ^ y := by
  have hc0 : 0 < c := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : 0 < y := hm0.trans_le hmy
  have hK : 0 ≤ K := (Nat.cast_nonneg M).trans hMK
  have h1 : ((M + m).choose m : ℝ) ≤ ((M : ℝ) + m) ^ m / m.factorial := by
    have := Nat.choose_le_pow_div (α := ℝ) m (M + m)
    push_cast at this
    exact this
  have h2 : (m : ℝ) ^ m / m.factorial ≤ Real.exp m := Real.pow_div_factorial_le_exp hm0.le m
  have h3 : ((M : ℝ) + m) ^ m / m.factorial =
      (1 + (M : ℝ) / m) ^ m * ((m : ℝ) ^ m / m.factorial) := by
    rw [← mul_div_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ _ hm0.ne']
  have h4 : (1 + (M : ℝ) / m) ^ m ≤ (1 + K / m) ^ m :=
    pow_le_pow_left₀ (by positivity)
      (by have := div_le_div_of_nonneg_right hMK hm0.le; linarith) m
  have hC : ((M + m).choose m : ℝ) ≤ (1 + K / m) ^ m * Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    calc ((M + m).choose m : ℝ) ≤ ((M : ℝ) + m) ^ m / m.factorial := h1
      _ = (1 + (M : ℝ) / m) ^ m * ((m : ℝ) ^ m / m.factorial) := h3
      _ ≤ (1 + K / m) ^ m * Real.exp m := mul_le_mul h4 h2 (by positivity) (by positivity)
  have hce : 1 ≤ c * Real.exp 1 := by
    have := Real.add_one_le_exp 1
    nlinarith
  calc c ^ m * ((M + m).choose m : ℝ) ≤ c ^ m * ((1 + K / m) ^ m * Real.exp 1 ^ m) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (c * Real.exp 1) ^ (m : ℝ) * (1 + K / m) ^ (m : ℝ) := by
        rw [Real.rpow_natCast, Real.rpow_natCast, mul_pow]
        ring
    _ ≤ (c * Real.exp 1) ^ y * (1 + K / y) ^ y :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hce hmy) (one_add_div_rpow_le hK hm0 hmy)
          (by positivity) (by positivity)
    _ = (c * Real.exp 1 * (1 + K / y)) ^ y := (Real.mul_rpow (by positivity) (by positivity)).symm

theorem rhoR_nonneg {r : ℝ} (hr : 1 < r) {α : ℝ} (hα : 0 < α) : 0 ≤ rhoR r α := by
  have hr1 : 0 < r - 1 := by linarith
  exact mul_nonneg (div_nonneg (by linarith) (by positivity))
    (Real.rpow_nonneg (by have := div_pos (mul_pos hα (by linarith : (0 : ℝ) < r)) hr1
                          positivity) _)

theorem rhoR_pow {r : ℝ} (hr : 1 < r) {α : ℝ} (hα : 0 < α) (k : ℕ) :
    rhoR r α ^ k = (4 * (r - 1) / r ^ 2) ^ k *
      (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ ((k : ℝ) / α) := by
  have hr1 : 0 < r - 1 := by linarith
  have hQ : 0 ≤ 2 * r * Real.exp 1 * (α * r / (r - 1) + 1) := by
    have := div_pos (mul_pos hα (by linarith : (0 : ℝ) < r)) hr1
    positivity
  rw [rhoR, mul_pow, ← Real.rpow_natCast ((2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ (1 / α)) k,
    ← Real.rpow_mul hQ, one_div_mul_eq_div]

/-- `Ξ(k) ≤ ρ(α)^k (4√(kr)/(r - 1) + 1)` for `n - 1 ≤ k/α`. -/
theorem xiK_le_rho {r : ℝ} (hr : 1 < r) {α : ℝ} (hα : 0 < α) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hnk : (n : ℝ) - 1 ≤ k / α) :
    xiK r n k ≤ rhoR r α ^ k * (4 * Real.sqrt (k * r) / (r - 1) + 1) := by
  have hr1 : 0 < r - 1 := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hαr : 0 < α * r / (r - 1) := div_pos (mul_pos hα (by linarith)) hr1
  have hQ1 : 1 ≤ 2 * r * Real.exp 1 * (α * r / (r - 1) + 1) := by
    have := Real.add_one_le_exp 1
    have h2 : 1 ≤ 2 * r * Real.exp 1 := by nlinarith
    nlinarith
  have hs0 : 0 ≤ 4 * Real.sqrt (k * r) / (r - 1) + 1 := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg (k * r))) hr1.le
    linarith
  have hθ : 0 ≤ 4 * (r - 1) / r ^ 2 := div_nonneg (by linarith) (by positivity)
  -- `(2r)^{n-1} binom(M + n - 1, n - 1) ≤ (2re(αr/(r - 1) + 1))^{k/α}`
  have key : (2 * r) ^ (n - 1) * ((mK r k + (n - 1)).choose (n - 1) : ℝ) ≤
      (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ ((k : ℝ) / α) := by
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h, Nat.sub_self, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      exact Real.one_le_rpow hQ1 (by positivity)
    have hM : (mK r k : ℝ) ≤ k * r / (r - 1) := by
      have h1 := Nat.floor_le (show 0 ≤ ((k : ℝ) - 1) * r / (r - 1) from
        div_nonneg (mul_nonneg (by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                   linarith) (by linarith)) hr1.le)
      rw [mK]
      push_cast
      have e : (k : ℝ) * r / (r - 1) = ((k : ℝ) - 1) * r / (r - 1) + r / (r - 1) := by ring
      have hr' : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ hr1]; linarith
      linarith
    have hm : ((n - 1 : ℕ) : ℝ) ≤ k / α := by rw [Nat.cast_sub hn, Nat.cast_one]; exact hnk
    have := pow_choose_le (c := 2 * r) (by linarith) (M := mK r k) (m := n - 1) (by omega) hM hm
    have e : (k : ℝ) * r / (r - 1) / (k / α) = α * r / (r - 1) := by
      have := hk0.ne'
      have := hα.ne'
      have := hr1.ne'
      field_simp
    rw [e, add_comm (1 : ℝ)] at this
    exact this
  calc xiK r n k = (4 * (r - 1) / r ^ 2) ^ k *
        ((2 * r) ^ (n - 1) * ((mK r k + (n - 1)).choose (n - 1) : ℝ)) *
        (4 * Real.sqrt (k * r) / (r - 1) + 1) := by
        rw [xiK, show mK r k + n - 1 = mK r k + (n - 1) by omega]
        ring
    _ ≤ (4 * (r - 1) / r ^ 2) ^ k *
        (2 * r * Real.exp 1 * (α * r / (r - 1) + 1)) ^ ((k : ℝ) / α) *
        (4 * Real.sqrt (k * r) / (r - 1) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (pow_nonneg hθ k)) hs0
    _ = rhoR r α ^ k * (4 * Real.sqrt (k * r) / (r - 1) + 1) := by rw [rhoR_pow hr hα]

/-- For `0 ≤ ρ < 1`, eventually `ρ^k (4√(kr)/(r - 1) + 1) ≤ 3(2 - r)^2/r^2`. -/
theorem exists_rho_small {r : ℝ} (hr : 1 < r) (hr2 : r < 2) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ρ ^ k * (4 * Real.sqrt (k * r) / (r - 1) + 1) ≤ 3 * (2 - r) ^ 2 / r ^ 2 := by
  have hr1 : 0 < r - 1 := by linarith
  have hc : 0 < 4 * Real.sqrt r / (r - 1) + 1 := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg r)) hr1.le
    linarith
  have hb : 0 < 3 * (2 - r) ^ 2 / r ^ 2 :=
    div_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) (by positivity)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    ((tendsto_self_mul_const_pow_of_lt_one hρ0 hρ).eventually (gt_mem_nhds (div_pos hb hc)))
  refine ⟨max K 1, fun k hk => ?_⟩
  have h1 : (k : ℝ) * ρ ^ k < 3 * (2 - r) ^ 2 / r ^ 2 / (4 * Real.sqrt r / (r - 1) + 1) :=
    hK k (le_of_max_le_left hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_of_max_le_right hk
  have hsk : Real.sqrt k ≤ k := by
    have := Real.sqrt_le_sqrt (show (k : ℝ) ≤ (k : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  have hs : 4 * Real.sqrt (k * r) / (r - 1) + 1 ≤ (4 * Real.sqrt r / (r - 1) + 1) * k := by
    rw [Real.sqrt_mul (Nat.cast_nonneg k)]
    have e : 4 * (Real.sqrt k * Real.sqrt r) / (r - 1) =
        Real.sqrt k * (4 * Real.sqrt r / (r - 1)) := by ring
    have := mul_le_mul_of_nonneg_right hsk
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg r)) hr1.le)
    rw [e]
    nlinarith
  calc ρ ^ k * (4 * Real.sqrt (k * r) / (r - 1) + 1)
      ≤ ρ ^ k * ((4 * Real.sqrt r / (r - 1) + 1) * k) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg hρ0 k)
    _ = (4 * Real.sqrt r / (r - 1) + 1) * (k * ρ ^ k) := by ring
    _ ≤ (4 * Real.sqrt r / (r - 1) + 1) *
          (3 * (2 - r) ^ 2 / r ^ 2 / (4 * Real.sqrt r / (r - 1) + 1)) :=
        mul_le_mul_of_nonneg_left h1.le hc.le
    _ = 3 * (2 - r) ^ 2 / r ^ 2 := by field_simp

/-- Proposition 6.8(c) of `coefficient-mass-rows.tex`: if `ρ(α) < 1`, there is `K` with
`V_r(n + k - 1, k) = 1/ν_k(n)` (and `ν_i(n) ≤ ν_k(n)` for `i ≤ k`) for every `n ≥ 1` and every
`k ≥ max(K, α(n - 1))`. -/
theorem longDiagC {r : ℝ} (hr : 1 < r) (hr2 : r < 2) {α : ℝ} (hα : 0 < α) (hρ : rhoR r α < 1) :
    ∃ K : ℕ, ∀ n k : ℕ, 1 ≤ n → K ≤ k → α * ((n : ℝ) - 1) ≤ k →
      rowValue r (n + k - 1) k = 1 / nuR r k n ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ k → nuR r i n ≤ nuR r k n := by
  obtain ⟨K, hK⟩ := exists_rho_small hr hr2 (rhoR_nonneg hr hα) hρ
  refine ⟨max K 2, fun n k hn hk hαk => ?_⟩
  have hk2 : 2 ≤ k := le_of_max_le_right hk
  have hnk : (n : ℝ) - 1 ≤ k / α := by
    rw [le_div_iff₀ hα]
    linarith
  have hΞ := (xiK_le_rho hr hα hn (by omega) hnk).trans (hK k (le_of_max_le_left hk))
  obtain ⟨hmono, hV, -⟩ := longDiag r hr n k hn hk2 (nK_le_tauR hr hr2 hn hk2 hΞ)
  exact ⟨hV, hmono⟩

end CoefficientMass
