/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly

/-!
# Far Zeros Keep the Last Prefix Sum Largest

This module proves Lemma 6.6 of `coefficient-mass-rows.tex`.  With
`w_k(s) = ω_k(s) - ω_{k-1}(s)`, `τ_k(n) = inf_{p ∈ Q_n} ∑_{s ≥ 2k-2} w_k(s) |p(s)|` and
`N_k(r) = max_{1 ≤ i < k} ∑_{s ≤ 2k-3} (ω_i(s) - ω_k(s))^+`, every `p = r_Y` with `Y` a set of
`n - 1` integers at least `k` has `A_k(p) - A_i(p) ≥ τ_k(n) - N_k(r)` for `1 ≤ i < k`: below
`2k - 2` the values `|p(s)|` are at most `1`, and from `2k - 2` on `ω_i ≤ ω_{k-1}`.

## Definitions

* `wDiff`.
* `tauR`.
* `nK`.
* `FarPrefix`.

## Theorems

* `choose_le_choose_succ`.
* `prefixWeight_le_prev`.
* `wDiff_nonneg`.
* `farPrefix`.
-/

open Polynomial

namespace CoefficientMass

/-- `w_k(s) = ω_k(s) - ω_{k-1}(s)`. -/
noncomputable def wDiff (r : ℝ) (k s : ℕ) : ℝ :=
  prefixWeight r k s - prefixWeight r (k - 1) s

/-- `τ_k(n) = inf_{p ∈ Q_n} ∑_{s ≥ 2k-2} w_k(s) |p(s)|`, indexed by `s = j + 2k - 2`. -/
noncomputable def tauR (r : ℝ) (k n : ℕ) : ℝ :=
  ⨅ p : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1},
    ∑' j : ℕ, wDiff r k (j + (2 * k - 2)) * |p.1.eval ((j + (2 * k - 2) : ℕ) : ℝ)|

/-- `N_k(r) = max_{1 ≤ i < k} ∑_{s ≤ 2k-3} (ω_i(s) - ω_k(s))^+` (the term `s = 0` is `0`). -/
noncomputable def nK (r : ℝ) (k : ℕ) : ℝ :=
  (Finset.Icc 1 (k - 1)).fold max 0 fun i =>
    ∑ s ∈ Finset.range (2 * k - 2), max (prefixWeight r i s - prefixWeight r k s) 0

/-- Lemma 6.6 of `coefficient-mass-rows.tex`: for `r > 1`, `k ≥ 2`, `n ≥ 1` and a set `Y` of
`n - 1` integers at least `k`, `A_k(r_Y) - A_i(r_Y) ≥ τ_k(n) - N_k(r)` for `1 ≤ i < k`. -/
def FarPrefix : Prop :=
  ∀ r : ℝ, 1 < r → ∀ k n : ℕ, 2 ≤ k → 1 ≤ n → ∀ Y : Finset ℕ, Y.card + 1 = n →
    (∀ y ∈ Y, k ≤ y) → ∀ i : ℕ, 1 ≤ i → i < k →
      tauR r k n - nK r k ≤ prefA r k (confPolyP Y) - prefA r i (confPolyP Y)

/-- `binom(n, j) ≤ binom(n, j + 1)` for `2j + 1 ≤ n`. -/
theorem choose_le_choose_succ {n j : ℕ} (h : 2 * j + 1 ≤ n) : n.choose j ≤ n.choose (j + 1) := by
  have := Nat.choose_succ_right_eq n j
  refine Nat.le_of_mul_le_mul_right
    (?_ : n.choose j * (j + 1) ≤ n.choose (j + 1) * (j + 1)) (by omega)
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)

/-- `ω_i(s) ≤ ω_{k-1}(s)` for `1 ≤ i ≤ k - 1` and `s ≥ 2k - 2`. -/
theorem prefixWeight_le_prev (r : ℝ) {i k s : ℕ} (hi : 1 ≤ i) (hik : i < k) (hs : 2 * k - 2 ≤ s)
    (hr : 1 < r) : prefixWeight r i s ≤ prefixWeight r (k - 1) s := by
  unfold prefixWeight
  rw [if_pos (by omega), if_pos (by omega)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := choose_le_choose_of_le_half (s - 1) (i - 1) (k - 1 - i) (by omega)
  rw [show i - 1 + (k - 1 - i) = k - 1 - 1 by omega] at this
  exact_mod_cast this

/-- `w_k(s) ≥ 0` for `s ≥ 2k - 2`, `k ≥ 2`. -/
theorem wDiff_nonneg (r : ℝ) (hr : 1 < r) {k s : ℕ} (hk : 2 ≤ k) (hs : 2 * k - 2 ≤ s) :
    0 ≤ wDiff r k s := by
  rw [wDiff, sub_nonneg]
  unfold prefixWeight
  rw [if_pos (by omega), if_pos (by omega)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := choose_le_choose_succ (n := s - 1) (j := k - 1 - 1) (by omega)
  rw [show k - 1 - 1 + 1 = k - 1 by omega] at this
  exact_mod_cast this

theorem farPrefix : FarPrefix := by
  intro r hr k n hk hn Y hYc hYk i hi hik
  have hY0 : 0 ∉ Y := fun h => by have := hYk 0 h; omega
  obtain ⟨hdeg, hp0, -⟩ := confPolyP_admissible (L := n) hY0 (by omega)
  have hpn : (confPolyP Y).natDegree < n := (natDegree_confPolyP Y).trans_lt (by omega)
  have hω : ∀ j s, 0 ≤ prefixWeight r j s := fun j s => (prefixWeight_le hr j s).1
  have hsum : ∀ j, Summable fun s : ℕ => prefixWeight r j s * |(confPolyP Y).eval (s : ℝ)| :=
    fun j => summable_weighted (hω j) (summable_weight_pow hr (prefixWeight_le hr j) (n - 1)) _
      fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  set g : ℕ → ℝ := fun s =>
    (prefixWeight r k s - prefixWeight r i s) * |(confPolyP Y).eval (s : ℝ)|
  have hg : Summable g := ((hsum k).sub (hsum i)).congr fun s => by simp only [g]; ring
  have hdiff : prefA r k (confPolyP Y) - prefA r i (confPolyP Y) =
      ∑ s ∈ Finset.range (2 * k - 2), g s + ∑' j, g (j + (2 * k - 2)) := by
    rw [hg.sum_add_tsum_nat_add (2 * k - 2), prefA, prefA, ← (hsum k).tsum_sub (hsum i)]
    exact tsum_congr fun s => by simp only [g]; ring
  -- positions below `2k - 2`
  have hlow : -nK r k ≤ ∑ s ∈ Finset.range (2 * k - 2), g s := by
    have hle : ∑ s ∈ Finset.range (2 * k - 2),
        max (prefixWeight r i s - prefixWeight r k s) 0 ≤ nK r k :=
      (Finset.le_fold_max _).2 (Or.inr ⟨i, Finset.mem_Icc.2 ⟨hi, by omega⟩, le_rfl⟩)
    rw [neg_le, ← Finset.sum_neg_distrib]
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) hle
    have hs := Finset.mem_range.1 hs
    have hp1 : |(confPolyP Y).eval (s : ℝ)| ≤ 1 := abs_confPolyP_le_one (Nat.cast_nonneg s)
      fun y hy => ⟨by have := hYk y hy; omega, by
        have := hYk y hy
        exact_mod_cast (show s ≤ 2 * y by omega)⟩
    have hp0' := abs_nonneg ((confPolyP Y).eval (s : ℝ))
    simp only [g]
    rcases le_total 0 (prefixWeight r k s - prefixWeight r i s) with h | h
    · nlinarith [le_max_right (prefixWeight r i s - prefixWeight r k s) 0]
    · nlinarith [le_max_left (prefixWeight r i s - prefixWeight r k s) 0]
  -- positions from `2k - 2` on
  have hwsum : Summable fun j : ℕ =>
      wDiff r k (j + (2 * k - 2)) * |(confPolyP Y).eval ((j + (2 * k - 2) : ℕ) : ℝ)| :=
    ((summable_nat_add_iff (2 * k - 2)).2 ((hsum k).sub (hsum (k - 1)))).congr fun j => by
      simp only [wDiff]
      ring
  have hhigh : tauR r k n ≤ ∑' j, g (j + (2 * k - 2)) := by
    refine (ciInf_le ⟨0, ?_⟩ (⟨confPolyP Y, hdeg, hp0⟩ :
      {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})).trans ?_
    · rintro _ ⟨p, rfl⟩
      exact tsum_nonneg fun j => mul_nonneg (wDiff_nonneg r hr hk (by omega)) (abs_nonneg _)
    · refine Summable.tsum_le_tsum (fun j => ?_) hwsum
        ((summable_nat_add_iff (2 * k - 2)).2 hg)
      simp only [g, wDiff]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      linarith [prefixWeight_le_prev r hi hik (show 2 * k - 2 ≤ j + (2 * k - 2) by omega) hr]
  rw [hdiff]
  linarith

end CoefficientMass
