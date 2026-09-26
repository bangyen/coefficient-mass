/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.AllUpper
import CoefficientMass.Chain
import CoefficientMass.LooseOrder
import CoefficientMass.QuadMass

/-!
# The Mass Infimum at Every Root Set

This module proves Corollary 4.3 of `coefficient-mass.tex`: for `L ≥ 2`,
`2 ≤ r_1 ≤ ⋯ ≤ r_L` and `P = ∏ (x - r_i)`, the infimum `M(P)` of `Λ(PQ)` over monic real
`Q` is `≍ L^2 + ∑_i i log (r_i - 1)`.  Every monic multiple has mass at least
`(L^2 + ∑_i i log (r_i - 1)) / 81`, by Proposition 4.2 for `L ≥ 8`, by (4.3) for
`L ≤ 7`, and by Corollary 3.4; and `Q = 1` has mass at most three times it.

## Definitions

* `AllRoots`.

## Theorems

* `mass_ge_sq`.
* `allRoots`.
-/

open Polynomial

namespace CoefficientMass

/-- Corollary 4.3: `M(P) ≍ L^2 + ∑_i i log (r_i - 1)`, with the constants `1/81` and `3`. -/
def AllRoots : Prop :=
  ∀ (L : ℕ) (r : Fin L → ℝ), 2 ≤ L → Monotone r → (∀ i, 2 ≤ r i) →
    (∀ Q : ℝ[X], Q.Monic →
      ((L : ℝ) ^ 2 + ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1)) / 81 ≤
        mass ((rootProduct ℝ r * Q).map (algebraMap ℝ ℂ))) ∧
    mass ((rootProduct ℝ r).map (algebraMap ℝ ℂ)) ≤
      3 * ((L : ℝ) ^ 2 + ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1))

/-- `Λ(F) ≥ L^2 / 80` for every monic multiple, `L ≥ 2`. -/
theorem mass_ge_sq {L : ℕ} (hL : 2 ≤ L) (r : Fin L → ℝ) (hmono : Monotone r)
    (hr : ∀ i, 2 ≤ r i) (F : ℝ[X]) (hF : F.Monic) (hdvd : rootProduct ℝ r ∣ F) :
    (L : ℝ) ^ 2 / 80 ≤ mass (F.map (algebraMap ℝ ℂ)) := by
  rcases le_or_gt 8 L with h8 | h8
  · exact quadraticMass L r F hF hr hdvd h8
  have hh := halfSum L r F (by omega) hmono hr hF hdvd
  have hS : (2 : ℝ) ≤ (∑ i, r i) / 2 := by
    have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hr i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have h2 : 1 ≤ largeCount F 2 := hh.trans (Finset.card_le_card fun j hj =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).1, hS.trans (Finset.mem_filter.1 hj).2⟩)
  have hm := largeCount_mul_log_le_mass F (by norm_num : (1 : ℝ) ≤ 2)
  have h2' : (1 : ℝ) ≤ largeCount F 2 := by exact_mod_cast h2
  have hlog := Real.log_two_gt_d9
  have hL7 : (L : ℝ) ≤ 7 := by exact_mod_cast (show L ≤ 7 by omega)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have k1 : Real.log 2 ≤ largeCount F 2 * Real.log 2 := le_mul_of_one_le_left (by linarith) h2'
  have k2 : (L : ℝ) ^ 2 ≤ 49 := by nlinarith
  linarith

/-- Corollary 4.3. -/
theorem allRoots : AllRoots := by
  intro L r hL hmono hr
  have hW0 : 0 ≤ ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) := Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith [hr i]))
  refine ⟨fun Q hQ => ?_, ?_⟩
  · have hF := (rootProduct_monic r).mul hQ
    have hdvd : rootProduct ℝ r ∣ rootProduct ℝ r * Q := dvd_mul_right _ _
    have hsq := mass_ge_sq hL r hmono hr _ hF hdvd
    have hlm := logarithmicMass L r ((rootProduct ℝ r * Q).map (algebraMap ℝ ℂ)) hmono hr
      (Polynomial.map_ne_zero hF.ne_zero)
      (by rw [rootProduct_complex]; exact Polynomial.map_dvd _ hdvd)
    rw [leadingCoeff_map, hF.leadingCoeff, map_one, norm_one, Real.log_one, mul_zero,
      zero_add] at hlm
    linarith
  · have hup := mass_rootProduct_le (by omega) r hmono hr
    have hconv : ∑ i ∈ Finset.range L, ((i : ℝ) + 1) *
        Real.log (r ⟨min i (L - 1), by omega⟩) =
          ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) *
        Real.log (r ⟨min i (L - 1), by omega⟩))]
      exact Finset.sum_congr rfl fun i _ => by
        rw [show (⟨min (i : ℕ) (L - 1), by omega⟩ : Fin L) = i from
          Fin.ext (Nat.min_eq_left (by omega))]
    have hlogr : ∀ i : Fin L, Real.log (r i) ≤ Real.log (r i - 1) + Real.log 2 := fun i => by
      rw [← Real.log_mul (by linarith [hr i]) two_ne_zero]
      exact Real.log_le_log (by linarith [hr i]) (by linarith [hr i])
    have hsum : ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i) ≤
        ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) + (L : ℝ) * L * Real.log 2 := by
      calc ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i)
          ≤ ∑ i : Fin L, (((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) + L * Real.log 2) :=
            Finset.sum_le_sum fun i _ => by
              have hi : ((i : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast i.isLt
              have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
              nlinarith [hlogr i]
        _ = ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) + (L : ℝ) * L * Real.log 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
    rw [hconv] at hup
    have hlog := Real.log_two_lt_d9
    have hlog0 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    have e1 : ((L : ℝ) + 1) * L * Real.log 2 ≤ ((L : ℝ) + 1) * L :=
      mul_le_of_le_one_right (by positivity) (by linarith)
    have e2 : (L : ℝ) * L * Real.log 2 ≤ L * L :=
      mul_le_of_le_one_right (by positivity) (by linarith)
    have e3 : (L : ℝ) ≤ L * L := le_mul_of_one_le_left (by linarith) hL1
    nlinarith

end CoefficientMass
