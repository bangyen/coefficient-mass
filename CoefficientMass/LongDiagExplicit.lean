/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.LongDiagC
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Every Diagonal Is Eventually Determined

This module states Proposition 6.8 of `coefficient-mass-rows.tex` in full and proves
Corollary 6.9.  Since `(2re(αr/(r - 1) + 1))^{1/α} → 1` as `α → ∞` and `θ < 1`, some `α ≥ 1`
has `ρ(α) < 1`; Proposition 6.8(c) then determines `V_r(L, L - n + 1)` for all large `L`.

## Definitions

* `LongDiagExplicit`.
* `LongDiagFinite`.

## Theorems

* `longDiagExplicit`.
* `exists_alpha`.
* `longDiagFinite`.
-/

open Filter Topology

namespace CoefficientMass

/-- Proposition 6.8 of `coefficient-mass-rows.tex`: for `1 < r < 2`, (a) `Ξ(k) ≤ 3(2 - r)^2/r^2`
gives `N_k(r) ≤ τ_k(n)`; (b) `Ξ(k + 1) ≤ γ_k Ξ(k)` with `γ_k` nonincreasing, so (a) holds for
every `k ≥ k_1` once `Ξ(k_1) ≤ 3(2 - r)^2/r^2` and `γ_{k_1} ≤ 1`; (c) if `ρ(α) < 1` then
`Ξ(k) ≤ ρ(α)^k (4√(kr)/(r - 1) + 1)` for `n - 1 ≤ k/α`, and some `K` has
`V_r(n + k - 1, k) = 1/ν_k(n)` for every `n ≥ 1` and `k ≥ max(K, α(n - 1))`. -/
def LongDiagExplicit : Prop :=
  ∀ r : ℝ, 1 < r → r < 2 →
    (∀ n k : ℕ, 1 ≤ n → 2 ≤ k → xiK r n k ≤ 3 * (2 - r) ^ 2 / r ^ 2 → nK r k ≤ tauR r k n) ∧
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      xiK r n (k + 1) ≤ gammaK r n k * xiK r n k ∧ gammaK r n (k + 1) ≤ gammaK r n k) ∧
    (∀ n k₁ : ℕ, 1 ≤ n → 2 ≤ k₁ → xiK r n k₁ ≤ 3 * (2 - r) ^ 2 / r ^ 2 → gammaK r n k₁ ≤ 1 →
      ∀ k : ℕ, k₁ ≤ k → nK r k ≤ tauR r k n) ∧
    ∀ α : ℝ, 1 ≤ α → rhoR r α < 1 →
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → (n : ℝ) - 1 ≤ k / α →
        xiK r n k ≤ rhoR r α ^ k * (4 * Real.sqrt (k * r) / (r - 1) + 1)) ∧
      ∃ K : ℕ, ∀ n k : ℕ, 1 ≤ n → K ≤ k → α * ((n : ℝ) - 1) ≤ k →
        rowValue r (n + k - 1) k = 1 / nuR r k n

/-- Corollary 6.9 of `coefficient-mass-rows.tex`: for `1 < r < 2` and `n ≥ 1`,
`V_r(L, L - n + 1) = 1/ν_{L-n+1}(n)` for all large `L`, and for all large `k`,
`ν_k(n) ≤ ν_{k+1}(n)` and `ν_k(n) = max_{i ≤ k} ν_i(n)`. -/
def LongDiagFinite : Prop :=
  ∀ r : ℝ, 1 < r → r < 2 → ∀ n : ℕ, 1 ≤ n →
    (∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → rowValue r L (L - n + 1) = 1 / nuR r (L - n + 1) n) ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      nuR r k n ≤ nuR r (k + 1) n ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k → nuR r i n ≤ nuR r k n

theorem longDiagExplicit : LongDiagExplicit := by
  intro r hr hr2
  refine ⟨fun n k hn hk h => nK_le_tauR hr hr2 hn hk h,
    fun n k hn hk => ⟨xiK_succ_le hr hn hk, gammaK_succ_le hr hn hk⟩,
    fun n k₁ hn hk₁ hΞ hγ k hk => nK_le_tauR hr hr2 hn (by omega)
      ((xiK_le_of_ge hr hn (by omega) hγ k hk).1.trans hΞ),
    fun α hα hρ => ⟨fun n k hn hk h => xiK_le_rho hr (by linarith) hn hk h, ?_⟩⟩
  obtain ⟨K, hK⟩ := longDiagC hr hr2 (by linarith) hρ
  exact ⟨K, fun n k hn hk h => (hK n k hn hk h).1⟩

/-- Some `α ≥ 1` has `ρ(α) < 1`. -/
theorem exists_alpha {r : ℝ} (hr : 1 < r) (hr2 : r < 2) : ∃ α : ℝ, 1 ≤ α ∧ rhoR r α < 1 := by
  have hr1 : 0 < r - 1 := by linarith
  have hθ : 4 * (r - 1) / r ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < 2 - r) 2]
  have hθ0 : 0 ≤ 4 * (r - 1) / r ^ 2 := div_nonneg (by linarith) (by positivity)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * r * Real.exp 1 * (r / (r - 1) + 1) := ⟨_, rfl⟩
  have hA : 0 < A := by
    have := div_pos (by linarith : (0 : ℝ) < r) hr1
    rw [hAdef]
    positivity
  have h1 : Tendsto (fun α : ℝ => A ^ (1 / α)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun α : ℝ => 1 / α) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hc : Tendsto (fun _ : ℝ => A) atTop (𝓝 A) := tendsto_const_nhds
    have := Filter.Tendsto.rpow hc h0 (Or.inl hA.ne')
    rwa [Real.rpow_zero] at this
  have h2 : Tendsto (fun α : ℝ => 4 * (r - 1) / r ^ 2 * (A ^ (1 / α) * α ^ (1 / α))) atTop
      (𝓝 (4 * (r - 1) / r ^ 2 * (1 * 1))) := (h1.mul tendsto_rpow_div).const_mul _
  rw [mul_one, mul_one] at h2
  obtain ⟨α, hlt, hα1⟩ := ((h2.eventually (gt_mem_nhds hθ)).and (eventually_ge_atTop 1)).exists
  refine ⟨α, hα1, lt_of_le_of_lt ?_ hlt⟩
  have hα0 : 0 < α := by linarith
  have hαr : 0 < α * r / (r - 1) := div_pos (mul_pos hα0 (by linarith)) hr1
  rw [rhoR, ← Real.mul_rpow hA.le hα0.le]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by positivity)) hθ0
  have hq : α * r / (r - 1) + 1 ≤ (r / (r - 1) + 1) * α := by
    have e : α * r / (r - 1) = r / (r - 1) * α := by ring
    rw [e]
    linarith
  calc 2 * r * Real.exp 1 * (α * r / (r - 1) + 1) ≤ 2 * r * Real.exp 1 * ((r / (r - 1) + 1) * α) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = A * α := by rw [hAdef]; ring

theorem longDiagFinite : LongDiagFinite := by
  intro r hr hr2 n hn
  obtain ⟨α, hα1, hρ⟩ := exists_alpha hr hr2
  obtain ⟨K, hK⟩ := longDiagC hr hr2 (by linarith) hρ
  obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K' = max (max K ⌈α * ((n : ℝ) - 1)⌉₊) 1 := ⟨_, rfl⟩
  have hgood : ∀ k : ℕ, K' ≤ k → rowValue r (n + k - 1) k = 1 / nuR r k n ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k → nuR r i n ≤ nuR r k n := fun k hk => by
    have h1 : K ≤ k := by omega
    have h2 : ⌈α * ((n : ℝ) - 1)⌉₊ ≤ k := by omega
    exact hK n k hn h1 ((Nat.le_ceil _).trans (by exact_mod_cast h2))
  have hK1 : 1 ≤ K' := by omega
  refine ⟨⟨n + K', fun L hL => ?_⟩, ⟨K', fun k hk => ⟨?_, (hgood k hk).2⟩⟩⟩
  · have := (hgood (L - n + 1) (by omega)).1
    rwa [show n + (L - n + 1) - 1 = L by omega] at this
  · exact (hgood (k + 1) (by omega)).2 k (by omega) (by omega)

end CoefficientMass
