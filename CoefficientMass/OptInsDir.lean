/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.InsShift
import CoefficientMass.TruncVertex

/-!
# The Direction of Lemma 5.2

This module prepares the optimality step of Lemma 5.2 of `coefficient-mass-rows.tex`.  With
`P = r_W`, `Q = r_{ins(W, c)}` and `κ = kappa W c`, the leading coefficient of `Q` is `-κ`
times that of `P`, so `H = P - Q - κ s P` has degree at most `|W|`, vanishes at `0` and on
`W ∩ [1, c - 1]`, and `P + ε H` is admissible.  Its values are `(1 + ε - εκs) P - ε Q`, and
since `P, Q` have equal signs below `c` (with `|Q| ≤ |P|`) and opposite signs from `c` on,
`|P + ε H|` is affine in `(|P|, |Q|)` at every position.

## Definitions

* `phiLt`.
* `phiGe`.

## Theorems

* `abs_sub_same_sign`.
* `abs_sub_opp_sign`.
* `degree_ins_dir_lt`.
* `phiD_split`.
-/

open Polynomial

namespace CoefficientMass

/-- `Φ_{r,D}^{<c}(q) = ∑_{1 ≤ s < c, s ≤ D} |q(s)| r^{-s}`. -/
noncomputable def phiLt (r : ℝ) (D c : ℕ) (q : ℝ[X]) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 D).filter (· < c), |q.eval (s : ℝ)| * (1 / r) ^ s

/-- `Φ_{r,D}^{≥c}(q) = ∑_{c ≤ s ≤ D} |q(s)| r^{-s}`. -/
noncomputable def phiGe (r : ℝ) (D c : ℕ) (q : ℝ[X]) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 D).filter (c ≤ ·), |q.eval (s : ℝ)| * (1 / r) ^ s

/-- Equal signs, `|q| ≤ |p|`, `α ≥ ε ≥ 0`: `|α p - ε q| = α |p| - ε |q|`. -/
theorem abs_sub_same_sign {p q α ε : ℝ} (hpq : 0 ≤ p * q) (hqp : |q| ≤ |p|) (hε : 0 ≤ ε)
    (hαε : ε ≤ α) : |α * p - ε * q| = α * |p| - ε * |q| := by
  rcases lt_trichotomy p 0 with hp | hp | hp
  · have hq : q ≤ 0 := by nlinarith
    rw [abs_of_neg hp, abs_of_nonpos hq] at hqp ⊢
    rw [abs_of_nonpos (by nlinarith)]
    ring
  · have hq : q = 0 := abs_nonpos_iff.1 (by rw [hp, abs_zero] at hqp; exact hqp)
    rw [hp, hq]
    simp only [mul_zero, sub_zero, abs_zero]
  · have hq : 0 ≤ q := by nlinarith
    rw [abs_of_pos hp, abs_of_nonneg hq] at hqp ⊢
    rw [abs_of_nonneg (by nlinarith)]

/-- Opposite signs, `α, ε ≥ 0`: `|α p - ε q| = α |p| + ε |q|`. -/
theorem abs_sub_opp_sign {p q α ε : ℝ} (hpq : p * q ≤ 0) (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    |α * p - ε * q| = α * |p| + ε * |q| := by
  rcases le_or_gt 0 p with hp | hp
  · rcases hp.eq_or_lt with hp0 | hp0
    · rw [← hp0, abs_zero, mul_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hε]
      ring
    · have hq : q ≤ 0 := by nlinarith
      rw [abs_of_pos hp0, abs_of_nonpos hq, abs_of_nonneg (by nlinarith)]
      ring
  · have hq : 0 ≤ q := by nlinarith
    rw [abs_of_neg hp, abs_of_nonneg hq, abs_of_nonpos (by nlinarith)]
    ring

/-- `deg (P - Q - κ s P) < |W| + 1`. -/
theorem degree_ins_dir_lt {W : Finset ℕ} {c : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hc1 : 1 ≤ c) :
    (confPolyP W - confPolyP (ins W c) - C (kappa W c) * X * confPolyP W).degree <
      (W.card + 1 : ℕ) := by
  have hP := natDegree_confPolyP W
  have hQ : (confPolyP (ins W c)).natDegree ≤ W.card + 1 := by
    have := natDegree_confPolyP (ins W c)
    rwa [card_ins hc] at this
  have hsum :
      (confPolyP (ins W c) + C (kappa W c) * X * confPolyP W).degree < (W.card + 1 : ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_add, mul_assoc, coeff_C_mul]
    rcases hm.eq_or_lt with hm' | hm'
    · rw [← hm', coeff_X_mul, coeff_ins_card h0 hc hc1]
      ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [coeff_X_mul, coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hm'),
        coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega)), mul_zero, add_zero]
  have hP' : (confPolyP W).degree < (W.card + 1 : ℕ) :=
    (degree_le_of_natDegree_le hP).trans_lt (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
  rw [sub_sub]
  exact (degree_sub_le _ _).trans_lt (max_lt hP' hsum)

theorem phiD_split (r : ℝ) (D c : ℕ) (q : ℝ[X]) :
    phiD r D q = phiLt r D c q + phiGe r D c q := by
  rw [phiD, phiLt, phiGe, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D) (· < c)]
  congr 1
  exact Finset.sum_congr (Finset.filter_congr fun x _ => not_lt) fun _ _ => rfl

end CoefficientMass
