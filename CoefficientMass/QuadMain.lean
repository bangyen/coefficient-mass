/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.QuadCoef
import CoefficientMass.QuadJensen
import CoefficientMass.QuadRev

/-!
# Jensen's Bound on the Rows

This module proves the bound (4.4) of Proposition 4.2 of `coefficient-mass.tex`: for a
monic multiple `F` of `∏ (x - r_i)` with `r_i ≥ 2`, `1 ≤ k ≤ L` and `1/2 < R < 1`,
`b_k(F) ≥ ((2R)^{L-k+1} - 1) / ((1 - R)^{-k} - 1)`.  If fewer than `k` nonleading
coefficients reach the bound `Y`, apply `T_z` at their backward distances `z` to the
reciprocal `F^*`: the result `g` has `g(0) = 1`, at least `L - k + 1` zeros in
`(0, 1/2]`, and `|g_d| ≤ Y C(d + k - 1, k - 1)` for `d ≥ 1`, so on `|t| = R` it stays
below `(2R)^{L-k+1}`, against Jensen's bound.

## Definitions

* `JensenRows`.

## Theorems

* `jensenRows`.
-/

open Polynomial

namespace CoefficientMass

/-- The bound (4.4) of Proposition 4.2: `b_k(F) ≥ ((2R)^{L-k+1} - 1) / ((1 - R)^{-k} - 1)`
for a monic multiple `F` of `∏ (x - r_i)`, `r_i ≥ 2`, `1 ≤ k ≤ L` and `1/2 < R < 1`. -/
def JensenRows : Prop :=
  ∀ (L k : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), F.Monic → (∀ i, 2 ≤ r i) → rootProduct ℝ r ∣ F →
    1 ≤ k → k ≤ L → ∀ R : ℝ, 1 / 2 < R → R < 1 →
      k ≤ largeCount F (((2 * R) ^ (L - k + 1) - 1) / (1 / (1 - R) ^ k - 1))

/-- Proposition 4.2, the bound (4.4). -/
theorem jensenRows : JensenRows := by
  intro L k r F hF hr hdvd hk hkL R hR1 hR2
  have hR0 : 0 < R := by linarith
  have h2R : 1 < 2 * R := by linarith
  have hT1 : 1 < 1 / (1 - R) ^ k :=
    one_lt_one_div (pow_pos (by linarith) k) (pow_lt_one₀ (by linarith) (by linarith) (by omega))
  have hnum : 0 < (2 * R) ^ (L - k + 1) - 1 := by
    have := one_lt_pow₀ h2R (by omega : L - k + 1 ≠ 0)
    linarith
  set Y := ((2 * R) ^ (L - k + 1) - 1) / (1 / (1 - R) ^ k - 1) with hY
  have hY0 : 0 < Y := div_pos hnum (by linarith)
  by_contra hlt
  push_neg at hlt
  set S := (Finset.range F.natDegree).filter fun j => Y ≤ ‖F.coeff j‖ with hS
  have hSk : S.card + 1 ≤ k := by
    have : largeCount F Y = S.card := rfl
    omega
  set Z := S.image fun j => F.natDegree - j with hZ
  have hZ1 : ∀ z ∈ Z, 1 ≤ z := fun z hz => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    omega
  have hZc : Z.card ≤ k - 1 := by
    have := Finset.card_image_le (s := S) (f := fun j => F.natDegree - j)
    omega
  have hcoeff : ∀ d, d ≤ F.natDegree → F.reverse.coeff d = F.coeff (F.natDegree - d) :=
    fun d hd => by rw [coeff_reverse, revAt_le hd]
  have hgc : ∀ d, (tOps Z.toList F.reverse).coeff d =
      F.reverse.coeff d * ∏ z ∈ Z, (1 - (d : ℝ) / z) := fun d => by
    rw [coeff_tOps, Finset.prod_toList]
  have hdeg : ∀ d, F.natDegree < d → (tOps Z.toList F.reverse).coeff d = 0 := fun d hd => by
    rw [hgc, coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le F).trans_lt hd), zero_mul]
  have hFs0 : F.reverse.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, hF.leadingCoeff]
  have hg0 : (tOps Z.toList F.reverse).eval 0 = 1 := by rw [eval_zero_tOps, hFs0]
  -- the zeros in `(0, 1/2]`
  have hL := card_rootsIn_reverse r hr F hF.ne_zero hdvd
  have hcnt := card_rootsIn_tOps F.reverse (by rw [hFs0]; norm_num) Z.toList
    fun z hz => hZ1 z (Finset.mem_toList.1 hz)
  rw [Finset.length_toList] at hcnt
  have hm : L - k + 1 ≤ Multiset.card (rootsIn (tOps Z.toList F.reverse)) := by omega
  -- the bound on the circle
  have hbound : ∀ t : ℂ, ‖t‖ = R → ‖((tOps Z.toList F.reverse).map (algebraMap ℝ ℂ)).eval t‖ ≤
      1 + Y * ∑ d ∈ Finset.range F.natDegree,
        ((d + 1 + (k - 1)).choose (k - 1) : ℝ) * R ^ (d + 1) := by
    intro t ht
    refine (norm_eval_le_sum hdeg ht).trans ?_
    rw [Finset.sum_range_succ', hgc 0, coeff_zero_reverse, hF.leadingCoeff, Nat.cast_zero]
    simp only [zero_div, sub_zero, Finset.prod_const_one, mul_one, abs_one, pow_zero]
    rw [add_comm, Finset.mul_sum]
    refine add_le_add_left (Finset.sum_le_sum fun d hd => ?_) 1
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hR0.le _)
    rw [hgc, abs_mul, Finset.abs_prod]
    have hd' := Finset.mem_range.1 hd
    have hP := prod_abs_le_choose (d + 1) Z hZ1 hZc
    by_cases hdZ : d + 1 ∈ Z
    · rw [Finset.prod_eq_zero hdZ (by
        rw [div_self (by positivity : ((d + 1 : ℕ) : ℝ) ≠ 0), sub_self, abs_zero]), mul_zero]
      exact mul_nonneg hY0.le (Nat.cast_nonneg _)
    · have hpos : F.natDegree - (d + 1) ∈ Finset.range F.natDegree :=
        Finset.mem_range.2 (by omega)
      have hnot : F.natDegree - (d + 1) ∉ S := fun h =>
        hdZ (Finset.mem_image.2 ⟨_, h, by omega⟩)
      have hlt' : |F.coeff (F.natDegree - (d + 1))| < Y := by
        by_contra hge
        push_neg at hge
        exact hnot (Finset.mem_filter.2 ⟨hpos, by rwa [Real.norm_eq_abs]⟩)
      rw [hcoeff (d + 1) (by omega)]
      exact mul_le_mul hlt'.le hP (Finset.prod_nonneg fun _ _ => abs_nonneg _) hY0.le
  -- Jensen's bound
  have hgne : tOps Z.toList F.reverse ≠ 0 := fun e => by
    rw [e, eval_zero] at hg0
    norm_num at hg0
  obtain ⟨H, hH⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hgne _).2
    (Multiset.filter_le _ (tOps Z.toList F.reverse).roots)
  have hJ := jensen_poly hR0 (rootsIn (tOps Z.toList F.reverse)) H _
    (fun a ha => (Multiset.mem_filter.1 ha).2) fun t ht => by
      rw [← hH]
      exact hbound t ht
  rw [← hH, eval_zero_map, hg0, map_one, norm_one, one_mul] at hJ
  have hsum := sum_choose_lt hR0 hR2 (k - 1) F.natDegree
  rw [Nat.sub_add_cancel hk] at hsum
  have hYT : Y * (1 / (1 - R) ^ k - 1) = (2 * R) ^ (L - k + 1) - 1 :=
    div_mul_cancel₀ _ (by linarith)
  have hpow := pow_le_pow_right₀ h2R.le hm
  linarith [mul_lt_mul_of_pos_left hsum hY0]

end CoefficientMass
