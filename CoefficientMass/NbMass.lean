/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.NbMoments
import CoefficientMass.NbNodes

/-!
# The Negative-Binomial Mass

This module proves Lemma 3.4 of `coefficient-mass-rows.tex`.  The law `P` has variance
`σ^2 = kr/(r - 1)^2`, so by Chebyshev's inequality at least `3/4` of its mass lies within
`2σ` of the mean, on at most `4σ + 1` integers; a mode carries at least
`3/(4(4√(kr)/(r - 1) + 1))`.

## Definitions

* `NbMass`.

## Theorems

* `nbLaw_mode_ge`.
* `nbMass`.
-/

namespace CoefficientMass

/-- Lemma 3.4 of `coefficient-mass-rows.tex`: for `r > 1`, `k, n ≥ 1` and a mode `M` of
`P(t) = binom(t - 1, k - 1) ϖ^k r^{-(t-k)}`, `M ≤ (k - 1)r/(r - 1) + 1`,
`ν_k(n)/a^k = (r - 1)^k ν_k(n) ≥ (n - 1)! P(M)/(r^{n-1} (2(M + n - 1))^{n-1})`, and
`P(M) ≥ 3/(4(4√(kr)/(r - 1) + 1))`. -/
def NbMass : Prop :=
  ∀ r : ℝ, 1 < r → ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → ∀ M : ℕ, (∀ t, nbLaw r k t ≤ nbLaw r k M) →
    (M : ℝ) ≤ ((k : ℝ) - 1) * r / (r - 1) + 1 ∧
    (n - 1).factorial * nbLaw r k M / (r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1)) ≤
      (r - 1) ^ k * nuR r k n ∧
    3 / (4 * (4 * Real.sqrt (k * r) / (r - 1) + 1)) ≤ nbLaw r k M

/-- A mode carries at least `3/(4(4√(kr)/(r - 1) + 1))`. -/
theorem nbLaw_mode_ge {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) {M : ℕ}
    (hM : ∀ t, nbLaw r k t ≤ nbLaw r k M) :
    3 / (4 * (4 * Real.sqrt (k * r) / (r - 1) + 1)) ≤ nbLaw r k M := by
  classical
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hr1 : 0 < r - 1 := by linarith
  have hK : ((c + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hr0 : r ≠ 0 := by positivity
  have hr1' : r - 1 ≠ 0 := hr1.ne'
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ((c + 1 : ℕ) : ℝ) * r / (r - 1) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 2 * Real.sqrt (((c + 1 : ℕ) : ℝ) * r) / (r - 1) := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ^ 2 = 4 * (((c + 1 : ℕ) : ℝ) * r / (r - 1) ^ 2) := by
    rw [hw, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hQ0 : ∀ j, 0 ≤ nbLaw r (c + 1) (j + (c + 1)) := fun j => nbLaw_nonneg hr _ _
  have hS0 := hasSum_nbLaw hr c
  have hV := hasSum_nbLaw_var hr c
  rw [← hμ] at hV
  set g : ℕ → ℝ := fun j =>
    if |((j + (c + 1) : ℕ) : ℝ) - μ| < w then nbLaw r (c + 1) (j + (c + 1)) else 0 with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [hg]
    split_ifs
    exacts [hQ0 j, le_rfl]
  have hgQ : ∀ j, g j ≤ nbLaw r (c + 1) (j + (c + 1)) := fun j => by
    simp only [hg]
    split_ifs
    exacts [le_rfl, hQ0 j]
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hgQ hS0.summable
  -- Chebyshev: the mass outside the window is at most `1/4`
  have hout : ∑' j, (nbLaw r (c + 1) (j + (c + 1)) - g j) ≤ 1 / 4 := by
    calc ∑' j, (nbLaw r (c + 1) (j + (c + 1)) - g j)
        ≤ ∑' j, nbLaw r (c + 1) (j + (c + 1)) * (((j + (c + 1) : ℕ) : ℝ) - μ) ^ 2 / w ^ 2 := by
          refine Summable.tsum_le_tsum (fun j => ?_) (hS0.summable.sub hgs)
            (hV.summable.div_const _)
          by_cases h : |((j + (c + 1) : ℕ) : ℝ) - μ| < w
          · simp only [hg, if_pos h, sub_self]
            exact div_nonneg (mul_nonneg (hQ0 j) (sq_nonneg _)) (sq_nonneg _)
          · simp only [hg, if_neg h, sub_zero]
            push_neg at h
            have : w ^ 2 ≤ (((j + (c + 1) : ℕ) : ℝ) - μ) ^ 2 := by
              rw [← sq_abs (((j + (c + 1) : ℕ) : ℝ) - μ)]
              exact pow_le_pow_left₀ hw0.le h 2
            rw [le_div_iff₀ (by positivity)]
            exact mul_le_mul_of_nonneg_left this (hQ0 j)
      _ = ((c + 1 : ℕ) : ℝ) * r / (r - 1) ^ 2 / w ^ 2 := (hV.div_const _).tsum_eq
      _ = 1 / 4 := by
          rw [hw2]
          field_simp
  have hin : 3 / 4 ≤ ∑' j, g j := by
    have h1 := hS0.tsum_eq
    rw [hS0.summable.tsum_sub hgs, h1] at hout
    linarith
  -- the window holds at most `2w + 1` integers
  set A := ⌈μ - w⌉₊
  set B := ⌊μ + w⌋₊
  have hwin : ∀ j, |((j + (c + 1) : ℕ) : ℝ) - μ| < w → A ≤ j + (c + 1) ∧ j + (c + 1) ≤ B :=
    fun j h => by
      obtain ⟨h1, h2⟩ := abs_lt.1 h
      exact ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩
  have hzero : ∀ j ∉ Finset.range (B + 1), g j = 0 := fun j hj => by
    simp only [hg]
    rw [if_neg]
    intro h
    exact hj (Finset.mem_range.2 (by have := (hwin j h).2; omega))
  set F := (Finset.range (B + 1)).filter fun j => |((j + (c + 1) : ℕ) : ℝ) - μ| < w
  have hsumF : ∑' j, g j ≤ F.card * nbLaw r (c + 1) M :=
    calc ∑' j, g j = ∑ j ∈ Finset.range (B + 1), g j := tsum_eq_sum hzero
      _ = ∑ j ∈ F, nbLaw r (c + 1) (j + (c + 1)) := (Finset.sum_filter _ _).symm
      _ ≤ F.card • nbLaw r (c + 1) M := Finset.sum_le_card_nsmul _ _ _ fun j _ => hM _
      _ = F.card * nbLaw r (c + 1) M := nsmul_eq_mul _ _
  have hcard : F.card ≤ (Finset.Icc A B).card :=
    Finset.card_le_card_of_injOn (fun j => j + (c + 1))
      (fun j hj => Finset.mem_Icc.2 (hwin j (Finset.mem_filter.1 hj).2))
      fun i _ j _ h => by
        have h' : i + (c + 1) = j + (c + 1) := h
        omega
  have hcardR : (F.card : ℝ) ≤ 2 * w + 1 := by
    have hA : μ - w ≤ A := Nat.le_ceil _
    have hB : (B : ℝ) ≤ μ + w := Nat.floor_le (by linarith)
    rw [Nat.card_Icc] at hcard
    refine (Nat.cast_le.2 hcard).trans ?_
    rcases le_total A (B + 1) with h | h
    · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
      linarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
      linarith
  have hkey : 3 / 4 ≤ (2 * w + 1) * nbLaw r (c + 1) M :=
    hin.trans (hsumF.trans (mul_le_mul_of_nonneg_right hcardR (nbLaw_nonneg hr _ _)))
  have e : 4 * Real.sqrt (((c + 1 : ℕ) : ℝ) * r) / (r - 1) = 2 * w := by
    rw [hw]
    ring
  rw [e, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (2 * w + 1))]
  calc (3 : ℝ) = 4 * (3 / 4) := by norm_num
    _ ≤ 4 * ((2 * w + 1) * nbLaw r (c + 1) M) := by linarith
    _ = nbLaw r (c + 1) M * (4 * (2 * w + 1)) := by ring

theorem nbMass : NbMass := fun r hr _ n hk hn M hM =>
  ⟨nbLaw_mode_le hr hk hM, nbLaw_nodes_le hr hn M, nbLaw_mode_ge hr hk hM⟩

end CoefficientMass
