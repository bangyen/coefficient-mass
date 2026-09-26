/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowPrefix

/-!
# The Weighted Problem `Ω_k`

This module proves the two inequalities about `Ω_k(n)` in the lower bound of Theorem 3.3
of `coefficient-mass-rows.tex`.  For `|S| = k - 1` and admissible `p`, the polynomial
`r_S p` is admissible for `μ_r(S, L)`, and Lemma 3.2 gives `|r_S| ≤ W_k`, so
`μ_r(S, L) ≤ Ω_k(n)`.  For `p = r_Y` with `Y ⊂ [k, ∞)` and `|Y| = n - 1`, `|p(s)| ≤ 1` for
`s ≤ 2k - 2`, and `W_k(s) = binom(s - 1, k - 1)` for `s ≥ 2k - 1`, so the sum defining `Ω_k`
is at most `E_k(r)` plus the sum defining `ν_k`; Lemma 3.1 then gives
`Ω_k(n) ≤ ν_k(n) + E_k(r)`.

## Theorems

* `wK_le_pow`.
* `omegaWeight_le`.
* `summable_weight_pow`.
* `muR_le_omegaR`.
* `abs_confPolyP_le_one`.
* `omegaR_le`.
-/

open Polynomial

namespace CoefficientMass

theorem wK_le_pow (k s : ℕ) : (wK k s : ℝ) ≤ (1 + (s : ℝ)) ^ (k - 1) := by
  rw [wK]
  calc (((s - 1).choose (min (k - 1) ((s - 1) / 2)) : ℕ) : ℝ)
      ≤ ((s - 1 : ℕ) : ℝ) ^ (min (k - 1) ((s - 1) / 2)) := by
        exact_mod_cast Nat.choose_le_pow _ _
    _ ≤ (1 + (s : ℝ)) ^ (min (k - 1) ((s - 1) / 2)) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by
          have : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
          linarith) _
    _ ≤ (1 + (s : ℝ)) ^ (k - 1) :=
        pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) s; linarith) (min_le_left _ _)

theorem omegaWeight_le {r : ℝ} (hr : 1 < r) (k s : ℕ) :
    0 ≤ omegaWeight r k s ∧ omegaWeight r k s ≤ (1 + (s : ℝ)) ^ (k - 1) * (1 / r) ^ s := by
  have hx : 0 < 1 / r := by positivity
  unfold omegaWeight
  split_ifs
  · exact ⟨by positivity, mul_le_mul_of_nonneg_right (wK_le_pow k s) (by positivity)⟩
  · exact ⟨le_rfl, by positivity⟩

/-- A weight below `(1 + s)^j r^{-s}` has `∑_s ω(s) (1 + s)^m < ∞`. -/
theorem summable_weight_pow {r : ℝ} (hr : 1 < r) {ω : ℕ → ℝ} {j : ℕ}
    (hω : ∀ s, 0 ≤ ω s ∧ ω s ≤ (1 + (s : ℝ)) ^ j * (1 / r) ^ s) (m : ℕ) :
    Summable fun s : ℕ => ω s * (1 + (s : ℝ)) ^ m := by
  have hx0 : 0 ≤ 1 / r := by positivity
  have hx1 : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr
  refine Summable.of_nonneg_of_le (fun s => mul_nonneg (hω s).1 (by positivity)) (fun s => ?_)
    (summable_poly_geom hx0 hx1 (j + m))
  calc ω s * (1 + (s : ℝ)) ^ m ≤ (1 + (s : ℝ)) ^ j * (1 / r) ^ s * (1 + (s : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_right (hω s).2 (by positivity)
    _ = (1 + (s : ℝ)) ^ (j + m) * (1 / r) ^ s := by rw [pow_add]; ring

/-- `μ_r(S, L) ≤ Ω_k(n)` for `|S| = k - 1`, `n = L - k + 1`. -/
theorem muR_le_omegaR {r : ℝ} (hr : 1 < r) {L k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L)
    {S : Finset ℕ} (h0 : 0 ∉ S) (hSc : S.card + 1 = k) :
    muR r S L ≤ omegaR r k (L - k + 1) := by
  haveI : Nonempty {p : ℝ[X] // p.degree < ↑(L - k + 1) ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast (show 0 < L - k + 1 by omega), eval_one⟩⟩
  refine le_ciInf fun p => ?_
  obtain ⟨p, hp, hp0⟩ := p
  change _ ≤ ∑' s : ℕ, omegaWeight r k s * |p.eval (s : ℝ)|
  have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
  have hpn : p.natDegree < L - k + 1 := by
    rw [degree_eq_natDegree hpne] at hp
    exact_mod_cast hp
  have hadm := confPolyP_admissible h0 (show S.card < k by omega)
  set q := confPolyP S * p
  have hq : q.degree < L := by
    have : q.natDegree ≤ S.card + p.natDegree :=
      (natDegree_mul_le (p := confPolyP S) (q := p)).trans
        (add_le_add (natDegree_confPolyP S) le_rfl)
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show q.natDegree < L by omega))
  have hq0 : q.eval 0 = 1 := by rw [eval_mul, hadm.2.1, hp0, one_mul]
  have hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0 := fun s hs => by rw [eval_mul, hadm.2.2 s hs, zero_mul]
  have hμ : muR r S L ≤ rowPhi r q := ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by
        have : 0 < 1 / r := by positivity
        positivity⟩
    (⟨q, hq, hq0, hqS⟩ : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})
  refine hμ.trans ?_
  rw [tsum_shift (by
    change omegaWeight r k 0 * _ = 0
    rw [omegaWeight, if_neg (by norm_num), zero_mul]), rowPhi]
  have hsum := summable_weighted (fun s => (omegaWeight_le hr k s).1)
    (summable_weight_pow hr (omegaWeight_le hr k) (L - k + 1 - 1)) _
    fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  refine Summable.tsum_le_tsum (fun d => ?_) (summable_rowPhi hr q)
    ((summable_nat_add_iff 1).2 hsum)
  have hW := (rowPointwise.1 S h0 (d + 1) (by omega)).2 k (by omega)
  rw [confPoly_eq_eval] at hW
  rw [eval_mul, abs_mul, omegaWeight, if_pos (by omega)]
  have hx : 0 ≤ (1 / r) ^ (d + 1) := by
    have : 0 < 1 / r := by positivity
    positivity
  calc |(confPolyP S).eval ((d + 1 : ℕ) : ℝ)| * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
      ≤ (wK k (d + 1) : ℝ) * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW (abs_nonneg _)) hx
    _ = _ := by ring

/-- `|r_Y(s)| ≤ 1` when `0 ≤ s ≤ 2y` for every `y ∈ Y`. -/
theorem abs_confPolyP_le_one {Y : Finset ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hY : ∀ y ∈ Y, 0 < y ∧ s ≤ 2 * y) : |(confPolyP Y).eval s| ≤ 1 := by
  rw [eval_confPolyP, Finset.abs_prod]
  refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun y hy => ?_
  obtain ⟨hy0, hsy⟩ := hY y hy
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy0
  have h1 : s / y ≤ 2 := by rw [div_le_iff₀ hy']; linarith
  have h2 : 0 ≤ s / y := div_nonneg hs hy'.le
  rw [abs_le]
  constructor <;> linarith

end CoefficientMass
