/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.AllUpper
import CoefficientMass.Chain

/-!
# Near-Optimality of the Root Product

This module proves Corollary 3.7 of `coefficient-mass.tex`: for `2 ≤ r_1 ≤ ⋯ ≤ r_L` and
`P = ∏ (x - r_i)`, every monic real `Q` has
`Λ(P) - Λ(PQ) ≤ ∑_k log C(L, k) + ∑_i i log (r_i / (r_i - 1)) ≤ (L^2 + L(L + 1)/2) log 2`.
The mass of `P` is at most `∑_k log C(L, k) + ∑_i i log r_i` by Vieta, and that of `PQ` at
least `∑_i i log (r_i - 1)` by Corollary 3.4.

## Definitions

* `NearOptimal`.

## Theorems

* `sum_range_extend`.
* `sum_log_choose_le`.
* `sum_succ_eq`.
* `nearOptimal`.
-/

open Polynomial

namespace CoefficientMass

/-- Corollary 3.7: `Λ(P) - Λ(PQ) ≤ ∑_k log C(L, k) + ∑_i i log (r_i / (r_i - 1))`, which is
at most `(L^2 + L(L + 1)/2) log 2`, for every monic real `Q`. -/
def NearOptimal : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ), 1 ≤ L → Monotone r → (∀ i, 2 ≤ r i) →
    (∀ Q : ℝ[X], Q.Monic →
      mass ((rootProduct ℝ r).map (algebraMap ℝ ℂ)) -
          mass ((rootProduct ℝ r * Q).map (algebraMap ℝ ℂ)) ≤
        ∑ k ∈ Finset.range (L + 1), Real.log (L.choose k) +
          ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i / (r i - 1))) ∧
    ∑ k ∈ Finset.range (L + 1), Real.log (L.choose k) +
        ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i / (r i - 1)) ≤
      ((L : ℝ) ^ 2 + L * (L + 1) / 2) * Real.log 2

theorem sum_range_extend {L : ℕ} (hL : 1 ≤ L) (r : Fin L → ℝ) :
    ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (r ⟨min i (L - 1), by omega⟩) =
      ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) *
    Real.log (r ⟨min i (L - 1), by omega⟩))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show (⟨min (i : ℕ) (L - 1), by omega⟩ : Fin L) = i from
      Fin.ext (Nat.min_eq_left (by omega))]

theorem sum_log_choose_le (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), Real.log (L.choose k) ≤ (L : ℝ) ^ 2 * Real.log 2 := by
  rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, Real.log_one, add_zero]
  calc ∑ k ∈ Finset.range L, Real.log (L.choose (k + 1))
      ≤ ∑ _k ∈ Finset.range L, (L : ℝ) * Real.log 2 := Finset.sum_le_sum fun k hk => by
        have hk := Finset.mem_range.1 hk
        calc Real.log (L.choose (k + 1)) ≤ Real.log ((2 : ℝ) ^ L) :=
              Real.log_le_log (by exact_mod_cast Nat.choose_pos (by omega))
                (by exact_mod_cast Nat.choose_le_two_pow L (k + 1))
          _ = L * Real.log 2 := Real.log_pow 2 L
    _ = (L : ℝ) ^ 2 * Real.log 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem sum_succ_eq : ∀ n : ℕ, ∑ i : Fin n, ((i : ℕ) + 1 : ℝ) = n * (n + 1) / 2 := by
  intro n
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty]; push_cast; ring
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- Corollary 3.7. -/
theorem nearOptimal : NearOptimal := by
  intro L r hL hmono hr
  have hlogdiv : ∀ i : Fin L, Real.log (r i / (r i - 1)) = Real.log (r i) - Real.log (r i - 1) :=
    fun i => Real.log_div (by linarith [hr i]) (by linarith [hr i])
  refine ⟨fun Q hQ => ?_, ?_⟩
  · have hF := (rootProduct_monic r).mul hQ
    have hdvd : rootProduct ℝ r ∣ rootProduct ℝ r * Q := dvd_mul_right _ _
    have hlm := logarithmicMass L r ((rootProduct ℝ r * Q).map (algebraMap ℝ ℂ)) hmono hr
      (Polynomial.map_ne_zero hF.ne_zero)
      (by rw [rootProduct_complex]; exact Polynomial.map_dvd _ hdvd)
    rw [leadingCoeff_map, hF.leadingCoeff, map_one, norm_one, Real.log_one, mul_zero,
      zero_add] at hlm
    have hup := mass_rootProduct_le_choose hL r hmono hr
    rw [sum_range_extend hL r] at hup
    have e : ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i / (r i - 1)) =
        ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i) -
          ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hlogdiv, mul_sub]
    rw [e]
    linarith
  · have h2 : ∀ i : Fin L, Real.log (r i / (r i - 1)) ≤ Real.log 2 := fun i =>
      Real.log_le_log (div_pos (by linarith [hr i]) (by linarith [hr i]))
        (by rw [div_le_iff₀ (by linarith [hr i])]; linarith [hr i])
    have hsum : ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i / (r i - 1)) ≤
        L * (L + 1) / 2 * Real.log 2 := by
      calc ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i / (r i - 1))
          ≤ ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log 2 :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h2 i) (by positivity)
        _ = L * (L + 1) / 2 * Real.log 2 := by rw [← Finset.sum_mul, sum_succ_eq]
    have := sum_log_choose_le L
    nlinarith

end CoefficientMass
