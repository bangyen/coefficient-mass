/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.BelowTwo
import CoefficientMass.LongDiagTau

/-!
# An Explicit Sufficient Condition for Long Diagonals

This module proves Proposition 6.8(a) of `coefficient-mass-rows.tex`.  First
`N_k(r) ≤ E_k(r) ≤ r^2/(4(2 - r)) (4/r^2)^k`.  At the mode `M_k = ⌊(k - 1)r/(r - 1)⌋ + 1`,
`ω_k(M_k) ≥ a^k · 3/(4(4√(kr)/(r - 1) + 1))` and the lower bound for `τ_k(n)` give
`N_k(r) ≤ τ_k(n)` as soon as `Ξ(k) ≤ 3(2 - r)^2/r^2`.

## Definitions

* `mK`.
* `xiK`.

## Theorems

* `nK_le_lossE`.
* `lt_mK`.
* `nK_le_tauR`.
-/

namespace CoefficientMass

/-- The mode `M_k = ⌊(k - 1)r/(r - 1)⌋ + 1`. -/
noncomputable def mK (r : ℝ) (k : ℕ) : ℕ :=
  ⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1

/-- `Ξ(k) = θ^k (2r)^{n-1} binom(M_k + n - 1, n - 1) (4√(kr)/(r - 1) + 1)`. -/
noncomputable def xiK (r : ℝ) (n k : ℕ) : ℝ :=
  (4 * (r - 1) / r ^ 2) ^ k * (2 * r) ^ (n - 1) * ((mK r k + n - 1).choose (n - 1) : ℝ) *
    (4 * Real.sqrt (k * r) / (r - 1) + 1)

/-- `N_k(r) ≤ E_k(r)`. -/
theorem nK_le_lossE {r : ℝ} (hr : 1 < r) (k : ℕ) : nK r k ≤ lossE r k := by
  have hω : ∀ j s, 0 ≤ prefixWeight r j s := fun j s => (prefixWeight_le hr j s).1
  refine (Finset.fold_max_le _).2 ⟨lossE_nonneg hr k, fun i _ => ?_⟩
  have h0 : prefixWeight r i 0 = 0 := by
    unfold prefixWeight
    rw [if_neg (by omega)]
  calc ∑ s ∈ Finset.range (2 * k - 2), max (prefixWeight r i s - prefixWeight r k s) 0
      ≤ ∑ s ∈ Finset.range (2 * k - 2), prefixWeight r i s :=
        Finset.sum_le_sum fun s _ => max_le (by linarith [hω k s]) (hω i s)
    _ ≤ ∑ s ∈ Finset.range (2 * k - 2 + 1), prefixWeight r i s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun s _ _ => hω i s
    _ = ∑ s ∈ Finset.range (2 * k - 2), prefixWeight r i (s + 1) := by
        rw [Finset.sum_range_succ', h0, add_zero]
    _ ≤ lossE r k := by
        rw [lossE, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
          Nat.add_sub_cancel]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [prefixWeight, if_pos (by omega), show 1 + s - 1 = s by omega, Nat.add_sub_cancel,
          add_comm 1 s]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_middle _ _)
          (by positivity)

theorem lt_mK (r : ℝ) (k : ℕ) : ((k : ℝ) - 1) * r / (r - 1) < mK r k := by
  rw [mK]
  push_cast
  exact Nat.lt_floor_add_one _

/-- Proposition 6.8(a) of `coefficient-mass-rows.tex`: for `1 < r < 2`, `n ≥ 1` and `k ≥ 2`,
`Ξ(k) ≤ 3(2 - r)^2/r^2` gives `N_k(r) ≤ τ_k(n)`. -/
theorem nK_le_tauR {r : ℝ} (hr : 1 < r) (hr2 : r < 2) {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hΞ : xiK r n k ≤ 3 * (2 - r) ^ 2 / r ^ 2) : nK r k ≤ tauR r k n := by
  have hr1 : 0 < r - 1 := by linarith
  have h2r : 0 < 2 - r := by linarith
  have hM := lt_mK r k
  have hτ := tauR_ge hr hr2.le hk hn hM
  have hmode : ∀ t, nbLaw r k t ≤ nbLaw r k (mK r k) := nbLaw_le_mode hr (by omega)
  have hP := nbLaw_mode_ge hr (by omega) hmode
  have hθ : (4 * (r - 1) / r ^ 2) ^ k = (4 / r ^ 2) ^ k * (r - 1) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [xiK, show mK r k + n - 1 = mK r k + (n - 1) by omega, mul_pow, hθ] at hΞ
  set M := mK r k
  set s := 4 * Real.sqrt (k * r) / (r - 1) + 1
  have hs : 0 < s := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg (k * r))) hr1.le
    linarith
  set Y := (4 / r ^ 2) ^ k
  set Z := (r - 1) ^ k
  set ω := prefixWeight r k M
  set D := r ^ (n - 1) * (2 ^ (n - 1) * ((M + (n - 1)).choose (n - 1) : ℝ))
  have hZ : 0 < Z := pow_pos hr1 k
  have hD : 0 < D := mul_pos (by positivity) (mul_pos (by positivity)
    (Nat.cast_pos.2 (Nat.choose_pos (by omega))))
  have hΞ' : Y * Z * D * s ≤ 3 * (2 - r) ^ 2 / r ^ 2 := le_of_eq_of_le (by ring) hΞ
  have hω3 : 3 ≤ 4 * s * Z * ω := by
    have : 3 / (4 * s) ≤ Z * ω := hP
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hmid : r ^ 2 / (4 * (2 - r)) * Y ≤ (2 - r) * ω / D := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hD]
    have hZs : 0 < Z * s := mul_pos hZ hs
    refine le_of_mul_le_mul_right
      (?_ : r ^ 2 * Y * D * (Z * s) ≤ (2 - r) * ω * (4 * (2 - r)) * (Z * s)) hZs
    calc r ^ 2 * Y * D * (Z * s) = r ^ 2 * (Y * Z * D * s) := by ring
      _ ≤ r ^ 2 * (3 * (2 - r) ^ 2 / r ^ 2) := mul_le_mul_of_nonneg_left hΞ' (sq_nonneg r)
      _ = 3 * (2 - r) ^ 2 := by field_simp
      _ ≤ (2 - r) ^ 2 * (4 * s * Z * ω) := by
          have := mul_le_mul_of_nonneg_left hω3 (sq_nonneg (2 - r))
          linarith
      _ = (2 - r) * ω * (4 * (2 - r)) * (Z * s) := by ring
  exact (nK_le_lossE hr k).trans ((lossE_le hr hr2 (by omega)).trans (hmid.trans hτ))

end CoefficientMass
