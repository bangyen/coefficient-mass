/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleInt
import CoefficientMass.TailExp
import CoefficientMass.TailJ
import CoefficientMass.TailProd
import CoefficientMass.TailSum

/-!
# The Tail Beyond the Kept Holes

This module proves Lemma 4.11 of `coefficient-mass.tex`.  For `s > N`,
`|ψ(s)| = C(s - 1, N) ∏_{c ∈ C} c / (s - c)`, and the product is at most
`(ℓ + 1) C(m, ℓ) ∫_0^1 t^ℓ (1 - t)^{s - m - 1} dt`.  Summing over `s`,
`Φ_tail ≤ (ℓ + 1) C(m, ℓ) ∫_0^1 t^ℓ (1 - t)^q (1 + t)^{-(N + 1)} dt`; the bound
`(q + 1) t (1 - t)^q ≤ e^{-1} (1 + t)^q` and the Beta bound for
`∫_0^1 t^{ℓ - 1} (1 + t)^{-(m + 1)} dt` give `Φ_tail ≤ (ℓ + 1) / (e ℓ (q + 1))`.

## Definitions

* `HoleTail`.

## Theorems

* `two_mul_le_of_card`.
* `tail_integral_le`.
* `holeTail`.
-/

open intervalIntegral

namespace CoefficientMass

/-- Lemma 4.11 (the tail beyond the kept holes): for `C = {c_1 < ⋯ < c_{ℓ+1}}` with
`c_1 = ℓ + 1`, `m = c_{ℓ+1}`, `N = m + q`, `ℓ ≥ 1` and `q ≥ 1`,
`∑_{s > N} |r_Y(s)| 2^{-s} ≤ (ℓ + 1) / (e ℓ (q + 1))` for `Y = {1, …, N} \ C`. -/
def HoleTail : Prop :=
  ∀ (ℓ q m : ℕ) (C : Finset ℕ), 1 ≤ ℓ → 1 ≤ q → C.card = ℓ + 1 → ℓ + 1 ∈ C → m ∈ C →
    (∀ c ∈ C, ℓ + 1 ≤ c ∧ c ≤ m) →
    ∑' t : ℕ, |confPoly (Finset.Icc 1 (m + q) \ C) (t + (m + q) + 1)| *
      (1 / 2 : ℝ) ^ (t + (m + q) + 1) ≤ (ℓ + 1) / (Real.exp 1 * ℓ * (q + 1))

/-- `ℓ + 1` points of `[ℓ + 1, m]` force `m ≥ 2ℓ + 1`. -/
theorem two_mul_le_of_card {ℓ m : ℕ} {C : Finset ℕ} (hC : C.card = ℓ + 1)
    (hCm : ∀ c ∈ C, ℓ + 1 ≤ c ∧ c ≤ m) : 2 * ℓ + 1 ≤ m := by
  have := Finset.card_le_card fun c (hc : c ∈ C) => Finset.mem_Icc.2 (hCm c hc)
  rw [Nat.card_Icc, hC] at this
  omega

/-- `(q + 1) ∫_0^1 t^{l+1} (1 - t)^q (1 + t)^{-(m + q + 1)} dt ≤ e^{-1} l! (m - l - 1)! / m!`. -/
theorem tail_integral_le {l q m : ℕ} (hq : 1 ≤ q) (hlm : l + 1 ≤ m) :
    ((q : ℝ) + 1) * ∫ x in (0 : ℝ)..1, x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1) ≤
      Real.exp (-1) * ((l.factorial * (m - (l + 1)).factorial : ℝ) / m.factorial) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact pow_ne_zero _ (by linarith [hx.1])
  have hmono : ∫ x in (0 : ℝ)..1, ((q : ℝ) + 1) *
      (x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1)) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (-1) * (x ^ l / (1 + x) ^ (m + 1)) := by
    refine integral_mono_on zero_le_one (hcont.intervalIntegrable.const_mul _)
      ((intervalIntegrable_jI l (m + 1)).const_mul _) fun x hx => ?_
    have h1x : (1 + x) ≠ 0 := by linarith [hx.1]
    have hw := tail_weight_le hq hx.1 hx.2
    have hg : 0 ≤ x ^ l / (1 + x) ^ (m + q + 1) :=
      div_nonneg (pow_nonneg hx.1 _) (pow_nonneg (by linarith [hx.1]) _)
    calc ((q : ℝ) + 1) * (x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1))
        = (((q : ℝ) + 1) * x * (1 - x) ^ q) * (x ^ l / (1 + x) ^ (m + q + 1)) := by ring
      _ ≤ (Real.exp (-1) * (1 + x) ^ q) * (x ^ l / (1 + x) ^ (m + q + 1)) :=
          mul_le_mul_of_nonneg_right hw hg
      _ = Real.exp (-1) * (x ^ l / (1 + x) ^ (m + 1)) := by
          rw [show m + q + 1 = m + 1 + q by omega, pow_add]
          field_simp
  rw [integral_const_mul, integral_const_mul] at hmono
  have hj := jI_le l (m - 1) (by omega)
  rw [show m - 1 + 2 = m + 1 by omega, show m - 1 - l = m - (l + 1) by omega,
    show m - 1 + 1 = m by omega] at hj
  exact hmono.trans (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le)

/-- Lemma 4.11 (the tail beyond the kept holes). -/
theorem holeTail : HoleTail := by
  intro ℓ q m C hℓ hq hC h1 hmC hCm
  obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by omega⟩
  have hm := two_mul_le_of_card hC hCm
  have h0 : 0 ∉ C := fun h => by have := (hCm 0 h).1; omega
  have hle : ∀ c ∈ C, c ≤ m + q := fun c hc => by have := (hCm c hc).2; omega
  have hP0 : 0 ≤ ∏ j ∈ Finset.range (l + 1), ((m : ℝ) - j) := Finset.prod_nonneg fun j hj => by
    have : (j : ℝ) ≤ m := by exact_mod_cast (show j ≤ m by have := Finset.mem_range.1 hj; omega)
    linarith
  set P := ∏ j ∈ Finset.range (l + 1), ((m : ℝ) - j) with hP
  set K : ℝ := (((l + 1 : ℕ) : ℝ) + 1) * P / ((l + 1).factorial : ℝ) with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (by positivity) hP0) (by positivity)
  -- each term
  have hterm : ∀ t : ℕ, |confPoly (Finset.Icc 1 (m + q) \ C) (t + (m + q) + 1)| *
      (1 / 2 : ℝ) ^ (t + (m + q) + 1) ≤ K * (((t + (m + q)).choose (m + q) : ℝ) *
        (1 / 2) ^ (t + (m + q) + 1) * betaI (l + 1) (t + q)) := by
    intro t
    rw [abs_confPoly_beyond h0 hle t]
    have hprod := prod_hole_div_le (s := t + (m + q) + 1) hC h1 (fun c hc => (hCm c hc).2) hm
      (by omega)
    have hb := betaI_mul_prod (l + 1) (t + q)
    have hbne : betaI (l + 1) (t + q) ≠ 0 := fun h => by
      rw [h, zero_mul] at hb
      exact (by positivity : (0 : ℝ) < ((l + 1).factorial : ℝ)).ne hb
    have hQ : ∏ j ∈ Finset.range (l + 1 + 1), (((t + (m + q) + 1 : ℕ) : ℝ) - m + j) =
        ∏ j ∈ Finset.range (l + 1 + 1), (((t + q : ℕ) : ℝ) + 1 + j) :=
      Finset.prod_congr rfl fun j _ => by push_cast; ring
    have hbeta : P / ∏ j ∈ Finset.range (l + 1 + 1), (((t + (m + q) + 1 : ℕ) : ℝ) - m + j) =
        P * betaI (l + 1) (t + q) / ((l + 1).factorial : ℝ) := by
      rw [hQ, ← hb, mul_comm (betaI (l + 1) (t + q)), mul_div_mul_right _ _ hbne]
    calc _ ≤ ((t + (m + q)).choose (m + q) : ℝ) * ((((l + 1 : ℕ) : ℝ) + 1) *
          (P / ∏ j ∈ Finset.range (l + 1 + 1), (((t + (m + q) + 1 : ℕ) : ℝ) - m + j))) *
          (1 / 2) ^ (t + (m + q) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))
          (by positivity)
      _ = K * (((t + (m + q)).choose (m + q) : ℝ) * (1 / 2) ^ (t + (m + q) + 1) *
          betaI (l + 1) (t + q)) := by
        rw [hbeta, hK]
        ring
  have hsumL : Summable fun t : ℕ => |confPoly (Finset.Icc 1 (m + q) \ C) (t + (m + q) + 1)| *
      (1 / 2 : ℝ) ^ (t + (m + q) + 1) :=
    (summable_nat_add_iff (m + q)).2 (summable_confTail _)
  have hHS := hasSum_tail_betaI (l + 1) q (m + q)
  have htail := tail_integral_le (l := l) (m := m) hq (by omega)
  have hI : ∫ x in (0 : ℝ)..1, x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1) ≤
      Real.exp (-1) * ((l.factorial * (m - (l + 1)).factorial : ℝ) / m.factorial) / (q + 1) := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact htail
  have hPf := prod_sub_mul_factorial (m := m) (l + 1) (by omega)
  have hP' : P = (m.factorial : ℝ) / ((m - (l + 1)).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    exact hPf
  calc ∑' t : ℕ, |confPoly (Finset.Icc 1 (m + q) \ C) (t + (m + q) + 1)| *
        (1 / 2 : ℝ) ^ (t + (m + q) + 1)
      ≤ ∑' t : ℕ, K * (((t + (m + q)).choose (m + q) : ℝ) * (1 / 2) ^ (t + (m + q) + 1) *
          betaI (l + 1) (t + q)) :=
        Summable.tsum_le_tsum hterm hsumL (hHS.summable.mul_left K)
    _ = K * ∫ x in (0 : ℝ)..1, x ^ (l + 1) * (1 - x) ^ q / (1 + x) ^ (m + q + 1) := by
        rw [tsum_mul_left, hHS.tsum_eq]
    _ ≤ K * (Real.exp (-1) * ((l.factorial * (m - (l + 1)).factorial : ℝ) / m.factorial) /
          (q + 1)) := mul_le_mul_of_nonneg_left hI hK0
    _ = (((l + 1 : ℕ) : ℝ) + 1) / (Real.exp 1 * ((l + 1 : ℕ) : ℝ) * (q + 1)) := by
        rw [hK, hP', Real.exp_neg, Nat.factorial_succ l]
        push_cast
        field_simp

end CoefficientMass
