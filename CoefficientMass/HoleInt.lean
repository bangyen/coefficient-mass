/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleProd

/-!
# The Hole Integral

This module proves Lemma 4.7 of `coefficient-mass.tex`.  For
`Y = {1, …, N} \ C` and `ψ = r_Y`, `Φ(Y)` splits at `N`.  Below `N` only the
holes `c ∈ C` contribute, with `|ψ(c)| = |π_c| ∫_0^1 v^{N - c} (1 - v)^{c - 1} dv`.
Beyond `N`, `|ψ(s)| = C(s - 1, N) ∏_{c ∈ C} c / (s - c)`, and partial fractions
turn the sum into `∑_{c ∈ C} π_c L(N, c)` with
`L(N, c) = 2^{-c} ∫_0^1 v^{N - c} (1 + v)^{c - 1} dv`.

## Definitions

* `HoleIntegral`.

## Theorems

* `abs_confPoly_hole`.
* `abs_confPoly_beyond`.
* `holeL_eq'`.
* `holeIntegral`.
-/

open Polynomial intervalIntegral

namespace CoefficientMass

/-- Lemma 4.7 (hole integral): for nonempty `C ⊆ {1, …, N}`,
`Φ({1, …, N} \ C) = ∫_0^1 ∑_{c ∈ C} 2^{-c} v^{N - c}
(π_c (1 + v)^{c - 1} + |π_c| (1 - v)^{c - 1}) dv`. -/
def HoleIntegral : Prop :=
  ∀ (N : ℕ) (C : Finset ℕ), C.Nonempty → 0 ∉ C → (∀ c ∈ C, c ≤ N) →
    confTail (Finset.Icc 1 N \ C) = ∫ v in (0 : ℝ)..1, ∑ c ∈ C, (1 / 2) ^ c * v ^ (N - c) *
      (holeWeight C c * (1 + v) ^ (c - 1) + |holeWeight C c| * (1 - v) ^ (c - 1))

/-- The value at a hole: `|ψ(c)| = |π_c| ∫_0^1 v^{N - c} (1 - v)^{c - 1} dv`. -/
theorem abs_confPoly_hole {N : ℕ} {C : Finset ℕ} (h0 : 0 ∉ C) (hle : ∀ c ∈ C, c ≤ N) {c : ℕ}
    (hc : c ∈ C) :
    |confPoly (Finset.Icc 1 N \ C) c| = |holeWeight C c| * betaI (N - c) (c - 1) := by
  have hsub : C ⊆ Finset.Icc 1 N := fun p hp =>
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hp), hle p hp⟩
  obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by
    have := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hc)
    omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = j + 1 + k := ⟨N - (j + 1), by have := hle _ hc; omega⟩
  have hY : |confPoly (Finset.Icc 1 (j + 1 + k) \ C) (j + 1)| =
      ∏ p ∈ Finset.Icc 1 (j + 1 + k) \ C, holeFactor (j + 1) p := by
    rw [confPoly, Finset.abs_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨hpI, hpC⟩ := Finset.mem_sdiff.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_Icc.1 hpI).1
    have hpc : p ≠ j + 1 := fun h => hpC (h ▸ hc)
    have e : (1 : ℝ) - ((j + 1 : ℕ) : ℝ) / p = (p - ((j + 1 : ℕ) : ℝ)) / p := by
      rw [sub_div, div_self hp0.ne']
    rw [holeFactor, if_neg hpc, e, abs_div, abs_of_pos hp0]
  have hE : ∀ p ∈ C.erase (j + 1), holeFactor (j + 1) p = |(p : ℝ) - ((j + 1 : ℕ) : ℝ)| / p :=
    fun p hp => by rw [holeFactor, if_neg (Finset.ne_of_mem_erase hp)]
  have h1 : holeFactor (j + 1) (j + 1) = 1 := by rw [holeFactor, if_pos rfl]
  have H := Finset.prod_sdiff (f := holeFactor (j + 1)) hsub
  rw [← Finset.prod_erase C h1, Finset.prod_congr rfl hE, Finset.prod_div_distrib,
    prod_holeFactor] at H
  have hPe : (0 : ℝ) < ∏ p ∈ C.erase (j + 1), |(p : ℝ) - ((j + 1 : ℕ) : ℝ)| :=
    Finset.prod_pos fun p hp => abs_pos.2 (sub_ne_zero.2 (by
      exact_mod_cast Finset.ne_of_mem_erase hp))
  have hQe : (0 : ℝ) < ∏ p ∈ C.erase (j + 1), (p : ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ Finset.mem_of_mem_erase hp)
  have hw : |holeWeight C (j + 1)| = ((j + 1 : ℕ) : ℝ) * (∏ p ∈ C.erase (j + 1), (p : ℝ)) /
      ∏ p ∈ C.erase (j + 1), |(p : ℝ) - ((j + 1 : ℕ) : ℝ)| := by
    rw [holeWeight, abs_div, Finset.abs_prod, Finset.abs_prod]
    simp only [Nat.abs_cast]
    rw [← Finset.mul_prod_erase C _ hc]
    exact congrArg _ (Finset.prod_congr rfl fun p _ => abs_sub_comm _ _)
  rw [hY, eq_div_of_mul_eq (div_ne_zero hPe.ne' hQe.ne') H, hw, betaI_eq,
    show j + 1 + k - (j + 1) = k by omega, Nat.add_sub_cancel, show k + j + 1 = j + 1 + k by ring]
  push_cast
  ring

/-- Beyond `N`: `|ψ(s)| = C(s - 1, N) ∏_{c ∈ C} c / (s - c)` at `s = t + N + 1`. -/
theorem abs_confPoly_beyond {N : ℕ} {C : Finset ℕ} (h0 : 0 ∉ C) (hle : ∀ c ∈ C, c ≤ N)
    (t : ℕ) : |confPoly (Finset.Icc 1 N \ C) (t + N + 1)| =
      ((t + N).choose N : ℝ) * ∏ c ∈ C, ((c : ℝ) / (((t + N + 1 : ℕ) : ℝ) - c)) := by
  have hsub : C ⊆ Finset.Icc 1 N := fun p hp =>
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hp), hle p hp⟩
  set s : ℝ := ((t + N + 1 : ℕ) : ℝ) with hs
  have hlt : ∀ p ∈ Finset.Icc 1 N, (0 : ℝ) < p ∧ (p : ℝ) < s := fun p hp => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hp
    exact ⟨by exact_mod_cast h1, by rw [hs]; exact_mod_cast (by omega : p < t + N + 1)⟩
  have H := Finset.prod_sdiff (f := fun p : ℕ => (s - p) / p) hsub
  rw [prod_Icc_sub_div] at H
  have hC : ∏ c ∈ C, (s - c) / (c : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c hc =>
    (div_pos (sub_pos.2 (hlt c (hsub hc)).2) (hlt c (hsub hc)).1).ne'
  rw [confPoly, Finset.abs_prod, Finset.prod_congr rfl fun p hp => by
    obtain ⟨hp0, hps⟩ := hlt p (Finset.mem_sdiff.1 hp).1
    rw [show (1 : ℝ) - s / p = -((s - p) / p) by rw [sub_div, div_self hp0.ne']; ring, abs_neg,
      abs_of_pos (div_pos (sub_pos.2 hps) hp0)], eq_div_of_mul_eq hC H, div_eq_mul_inv,
    ← Finset.prod_inv_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun c _ => inv_div _ _)

theorem holeL_eq' {N c : ℕ} (h1 : 1 ≤ c) (hc : c ≤ N) :
    holeL N c = (1 / 2) ^ c * plusI (N - c) (c - 1) := by
  have h := holeL_eq (c - 1) (N - c)
  rwa [show N - c + (c - 1) + 1 = N by omega, show c - 1 + 1 = c by omega] at h

/-- Lemma 4.7 (hole integral). -/
theorem holeIntegral : HoleIntegral := by
  intro N C hne h0 hle
  have hsub : C ⊆ Finset.Icc 1 N := fun p hp =>
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hp), hle p hp⟩
  set Y := Finset.Icc 1 N \ C
  have hc1 : ∀ c ∈ C, 1 ≤ c := fun c hc => (Finset.mem_Icc.1 (hsub hc)).1
  have hI : ∀ c ∈ C, ∫ v in (0 : ℝ)..1, (1 / 2) ^ c * v ^ (N - c) *
      (holeWeight C c * (1 + v) ^ (c - 1) + |holeWeight C c| * (1 - v) ^ (c - 1)) =
      holeWeight C c * holeL N c + |holeWeight C c| * betaI (N - c) (c - 1) * (1 / 2) ^ c :=
    fun c hc => by
      have h1 : IntervalIntegrable (fun v : ℝ => (1 / 2) ^ c * holeWeight C c *
          (v ^ (N - c) * (1 + v) ^ (c - 1))) MeasureTheory.volume 0 1 :=
        (by fun_prop : Continuous fun v : ℝ => (1 / 2) ^ c * holeWeight C c *
          (v ^ (N - c) * (1 + v) ^ (c - 1))).intervalIntegrable 0 1
      have h2 : IntervalIntegrable (fun v : ℝ => (1 / 2) ^ c * |holeWeight C c| *
          (v ^ (N - c) * (1 - v) ^ (c - 1))) MeasureTheory.volume 0 1 :=
        (by fun_prop : Continuous fun v : ℝ => (1 / 2) ^ c * |holeWeight C c| *
          (v ^ (N - c) * (1 - v) ^ (c - 1))).intervalIntegrable 0 1
      rw [integral_congr (g := fun v : ℝ => (1 / 2) ^ c * holeWeight C c *
          (v ^ (N - c) * (1 + v) ^ (c - 1)) + (1 / 2) ^ c * |holeWeight C c| *
          (v ^ (N - c) * (1 - v) ^ (c - 1))) fun v _ => by ring, integral_add h1 h2,
        integral_const_mul, integral_const_mul, holeL_eq' (hc1 c hc) (hle c hc), plusI, betaI]
      ring
  have hfin : ∑ d ∈ Finset.range N, |confPoly Y (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) =
      ∑ c ∈ C, |confPoly Y c| * (1 / 2 : ℝ) ^ c := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun s => |confPoly Y s| * (1 / 2 : ℝ) ^ s),
      zero_add, Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_sdiff hsub,
      Finset.sum_eq_zero fun p hp => ?_, zero_add]
    have hp0 : p ≠ 0 := by have := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hp).1).1; omega
    rw [confPoly, Finset.prod_eq_zero hp (by rw [div_self (by exact_mod_cast hp0), sub_self]),
      abs_zero, zero_mul]
  have e : ∀ t : ℕ, |confPoly Y (t + N + 1)| * (1 / 2 : ℝ) ^ (t + N + 1) =
      ∑ c ∈ C, holeWeight C c * (((t + N).choose N : ℝ) * (1 / 2) ^ (t + N + 1) /
        (((t + N + 1 : ℕ) : ℝ) - c)) := fun t => by
    rw [abs_confPoly_beyond h0 hle, prod_div_eq_sum hne fun c hc => (by
      exact_mod_cast (show c < t + N + 1 by have := hle c hc; omega) :
        (c : ℝ) < ((t + N + 1 : ℕ) : ℝ)).ne', Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have htail : ∑' t : ℕ, |confPoly Y (t + N + 1)| * (1 / 2 : ℝ) ^ (t + N + 1) =
      ∑ c ∈ C, holeWeight C c * holeL N c := by
    rw [tsum_congr e, Summable.tsum_finsetSum fun c hc => (summable_holeL (hle c hc)).mul_left _]
    exact Finset.sum_congr rfl fun c _ => by rw [tsum_mul_left, holeL]
  rw [integral_finset_sum fun c _ => (by fun_prop : Continuous fun v : ℝ => (1 / 2) ^ c *
    v ^ (N - c) * (holeWeight C c * (1 + v) ^ (c - 1) + |holeWeight C c| * (1 - v) ^ (c - 1))
    ).intervalIntegrable 0 1, Finset.sum_congr rfl hI, confTail,
    ← (summable_confTail Y).sum_add_tsum_nat_add N, hfin, htail, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c hc => by rw [abs_confPoly_hole h0 hle hc]; ring

end CoefficientMass
