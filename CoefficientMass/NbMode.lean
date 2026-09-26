/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly

/-!
# The Mode of the Negative-Binomial Law

This module proves the first claim of Lemma 3.4 of `coefficient-mass-rows.tex`.  The law
`P(t) = binom(t - 1, k - 1) ϖ^k r^{-(t-k)} = (r - 1)^k ω_k(t)` has
`P(t + 1)/P(t) = t/(r(t - k + 1)) ≥ 1/r`, so `P(M) ≤ r^l P(M + l)`, and a mode `M` has
`M ≤ (k - 1)r/(r - 1) + 1`.

## Definitions

* `nbLaw`.

## Theorems

* `nbLaw_nonneg`.
* `nbLaw_pos`.
* `nbLaw_le_succ`.
* `nbLaw_le_add`.
* `nbLaw_mul_self`.
* `nbLaw_mode_le`.
-/

open Polynomial

namespace CoefficientMass

/-- The negative-binomial law `P(t) = binom(t - 1, k - 1) ϖ^k r^{-(t-k)} = (r - 1)^k ω_k(t)`. -/
noncomputable def nbLaw (r : ℝ) (k t : ℕ) : ℝ :=
  (r - 1) ^ k * prefixWeight r k t

theorem nbLaw_nonneg {r : ℝ} (hr : 1 < r) (k t : ℕ) : 0 ≤ nbLaw r k t :=
  mul_nonneg (pow_nonneg (by linarith) k) (prefixWeight_le hr k t).1

theorem nbLaw_pos {r : ℝ} (hr : 1 < r) {k t : ℕ} (hk : 1 ≤ k) (hkt : k ≤ t) :
    0 < nbLaw r k t := by
  unfold nbLaw prefixWeight
  rw [if_pos (by omega)]
  exact mul_pos (pow_pos (by linarith) k)
    (mul_pos (by exact_mod_cast Nat.choose_pos (by omega)) (by positivity))

/-- `P(t) ≤ r P(t + 1)`. -/
theorem nbLaw_le_succ {r : ℝ} (hr : 1 < r) (k t : ℕ) : nbLaw r k t ≤ r * nbLaw r k (t + 1) := by
  have hx : 0 < 1 / r := by positivity
  have hr1 : 0 ≤ (r - 1) ^ k := pow_nonneg (by linarith) k
  unfold nbLaw prefixWeight
  rw [if_pos (show 1 ≤ t + 1 by omega)]
  split_ifs with ht
  · rw [pow_succ, Nat.add_sub_cancel]
    have : ((t - 1).choose (k - 1) : ℝ) ≤ (t.choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose _ (Nat.sub_le t 1)
    have hrr : r * (1 / r) = 1 := by field_simp
    calc (r - 1) ^ k * ((t - 1).choose (k - 1) * (1 / r) ^ t)
        ≤ (r - 1) ^ k * (t.choose (k - 1) * (1 / r) ^ t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by positivity)) hr1
      _ = r * ((r - 1) ^ k * (t.choose (k - 1) * ((1 / r) ^ t * (1 / r)))) := by
          linear_combination (-(r - 1) ^ k * t.choose (k - 1) * (1 / r) ^ t) * hrr
  · rw [mul_zero]
    exact mul_nonneg (by linarith) (mul_nonneg hr1 (by positivity))

/-- `P(M) ≤ r^l P(M + l)`. -/
theorem nbLaw_le_add {r : ℝ} (hr : 1 < r) (k M l : ℕ) :
    nbLaw r k M ≤ r ^ l * nbLaw r k (M + l) := by
  induction l with
  | zero => rw [pow_zero, one_mul, add_zero]
  | succ l ih =>
    rw [pow_succ, mul_assoc, ← add_assoc]
    exact ih.trans (mul_le_mul_of_nonneg_left (nbLaw_le_succ hr k (M + l)) (by positivity))

/-- `P(t) t = r (t - k + 1) P(t + 1)` for `t ≥ 1`. -/
theorem nbLaw_mul_self {r : ℝ} (hr : 1 < r) (k : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    nbLaw r k t * t = r * ((t - (k - 1) : ℕ) : ℝ) * nbLaw r k (t + 1) := by
  have h := Nat.choose_mul_succ_eq (t - 1) (k - 1)
  rw [Nat.sub_add_cancel ht] at h
  have h' : ((t - 1).choose (k - 1) : ℝ) * t = (t.choose (k - 1) : ℝ) * ((t - (k - 1) : ℕ) : ℝ) :=
    by exact_mod_cast h
  have hrr : r * (1 / r) = 1 := by field_simp
  unfold nbLaw prefixWeight
  rw [if_pos ht, if_pos (show 1 ≤ t + 1 by omega), Nat.add_sub_cancel, pow_succ]
  linear_combination (r - 1) ^ k * (1 / r) ^ t * h' -
    (r - 1) ^ k * (1 / r) ^ t * (t.choose (k - 1) : ℝ) * ((t - (k - 1) : ℕ) : ℝ) * hrr

/-- A mode `M` of `P` has `M ≤ (k - 1)r/(r - 1) + 1`. -/
theorem nbLaw_mode_le {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) {M : ℕ}
    (hM : ∀ t, nbLaw r k t ≤ nbLaw r k M) : (M : ℝ) ≤ ((k : ℝ) - 1) * r / (r - 1) + 1 := by
  by_contra h
  push_neg at h
  have hr1 : 0 < r - 1 := by linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hq : ((k : ℝ) - 1) * r / (r - 1) = (k - 1) + (k - 1) / (r - 1) := by
    field_simp
    ring
  have hq0 : 0 ≤ ((k : ℝ) - 1) / (r - 1) := div_nonneg hk1 hr1.le
  have hMk : k + 1 ≤ M := by
    have : ((k + 1 : ℕ) : ℝ) ≤ M := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨t, rfl⟩ : ∃ t, M = t + 1 := ⟨M - 1, by omega⟩
  have hkt : k ≤ t := by omega
  have ht : ((k : ℝ) - 1) * r / (r - 1) < t := by push_cast at h; linarith
  have ht' : ((k : ℝ) - 1) * r < t * (r - 1) := by rwa [div_lt_iff₀ hr1] at ht
  have hc : ((t - (k - 1) : ℕ) : ℝ) = t - k + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hk, Nat.cast_one]
    ring
  have hid := nbLaw_mul_self hr k (show 1 ≤ t by omega)
  rw [hc] at hid
  have hpos := nbLaw_pos hr hk hkt
  have hrt : (t : ℝ) < r * (t - k + 1) := by linarith
  have hkt' : (k : ℝ) ≤ t := by exact_mod_cast hkt
  have hrt0 : 0 ≤ r * ((t : ℝ) - k + 1) := mul_nonneg (by linarith) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left (hM t) hrt0
  have h2 := mul_lt_mul_of_pos_right hrt hpos
  linarith

end CoefficientMass
