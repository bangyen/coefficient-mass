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
`P(t + 1)/P(t) = t/(r(t - k + 1)) ≥ 1/r`, so `P(M) ≤ r^l P(M + l)`, a mode `M` has
`M ≤ (k - 1)r/(r - 1) + 1`, and `⌊(k - 1)r/(r - 1)⌋ + 1` is a mode.

## Definitions

* `nbLaw`.

## Theorems

* `nbLaw_nonneg`.
* `nbLaw_pos`.
* `nbLaw_le_succ`.
* `nbLaw_le_add`.
* `nbLaw_mul_self`.
* `nbLaw_mode_le`.
* `nbLaw_eq_zero`.
* `nbLaw_le_succ_of_le`.
* `nbLaw_succ_le_of_lt`.
* `nbLaw_le_mode`.
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
    have : (k : ℝ) < M := by linarith
    have : k < M := by exact_mod_cast this
    omega
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

/-- `P(t) = 0` for `t < k`. -/
theorem nbLaw_eq_zero (r : ℝ) {k t : ℕ} (ht : t < k) : nbLaw r k t = 0 := by
  unfold nbLaw prefixWeight
  split_ifs
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, mul_zero]
  · rw [mul_zero]

/-- `P(t) ≤ P(t + 1)` for `t ≤ (k - 1)r/(r - 1)`. -/
theorem nbLaw_le_succ_of_le {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) {t : ℕ}
    (ht : (t : ℝ) ≤ ((k : ℝ) - 1) * r / (r - 1)) : nbLaw r k t ≤ nbLaw r k (t + 1) := by
  rcases lt_or_ge t k with htk | htk
  · rw [nbLaw_eq_zero r htk]
    exact nbLaw_nonneg hr k _
  have hr1 : 0 < r - 1 := by linarith
  have ht' : (t : ℝ) * (r - 1) ≤ ((k : ℝ) - 1) * r := by rwa [le_div_iff₀ hr1] at ht
  have hc : ((t - (k - 1) : ℕ) : ℝ) = t - k + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hk, Nat.cast_one]
    ring
  have hid := nbLaw_mul_self hr k (show 1 ≤ t by omega)
  rw [hc] at hid
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hrt : r * ((t : ℝ) - k + 1) ≤ t := by linarith
  have h1 := mul_le_mul_of_nonneg_right hrt (nbLaw_nonneg hr k (t + 1))
  refine le_of_mul_le_mul_right (?_ : nbLaw r k t * t ≤ nbLaw r k (t + 1) * t) htpos
  linarith

/-- `P(t + 1) ≤ P(t)` for `t > (k - 1)r/(r - 1)`. -/
theorem nbLaw_succ_le_of_lt {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) {t : ℕ}
    (ht : ((k : ℝ) - 1) * r / (r - 1) < t) : nbLaw r k (t + 1) ≤ nbLaw r k t := by
  have hr1 : 0 < r - 1 := by linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hq : ((k : ℝ) - 1) * r / (r - 1) = (k - 1) + (k - 1) / (r - 1) := by
    field_simp
    ring
  have hq0 : 0 ≤ ((k : ℝ) - 1) / (r - 1) := div_nonneg hk1 hr1.le
  have hkt : k ≤ t := by
    have : (k : ℝ) < t + 1 := by linarith
    have : k < t + 1 := by exact_mod_cast this
    omega
  have ht' : ((k : ℝ) - 1) * r < t * (r - 1) := by rwa [div_lt_iff₀ hr1] at ht
  have hc : ((t - (k - 1) : ℕ) : ℝ) = t - k + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hk, Nat.cast_one]
    ring
  have hid := nbLaw_mul_self hr k (show 1 ≤ t by omega)
  rw [hc] at hid
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hrt : (t : ℝ) ≤ r * (t - k + 1) := by linarith
  have h1 := mul_le_mul_of_nonneg_right hrt (nbLaw_nonneg hr k (t + 1))
  refine le_of_mul_le_mul_right (?_ : nbLaw r k (t + 1) * t ≤ nbLaw r k t * t) htpos
  linarith

/-- `M_k = ⌊(k - 1)r/(r - 1)⌋ + 1` is a mode of `P`. -/
theorem nbLaw_le_mode {r : ℝ} (hr : 1 < r) {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    nbLaw r k t ≤ nbLaw r k (⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1) := by
  have hX : 0 ≤ ((k : ℝ) - 1) * r / (r - 1) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  set M := ⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1 with hM
  have up : ∀ d t, t + d = M → nbLaw r k t ≤ nbLaw r k M := by
    intro d
    induction d with
    | zero => exact fun t h => le_of_eq (by rw [← h, add_zero])
    | succ d ih =>
      intro t h
      refine (nbLaw_le_succ_of_le hr hk ?_).trans (ih (t + 1) (by omega))
      exact (Nat.le_floor_iff hX).1 (by omega)
  have down : ∀ d, nbLaw r k (M + d) ≤ nbLaw r k M := by
    intro d
    induction d with
    | zero => rw [add_zero]
    | succ d ih =>
      refine le_trans (nbLaw_succ_le_of_lt hr hk (t := M + d) ?_) ih
      have h1 := Nat.lt_floor_add_one (((k : ℝ) - 1) * r / (r - 1))
      have h2 : ((⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1 : ℕ) : ℝ) ≤ ((M + d : ℕ) : ℝ) := by
        exact_mod_cast (show ⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1 ≤ M + d by omega)
      push_cast at h2 ⊢
      linarith
  rcases le_total t M with h | h
  · exact up (M - t) t (by omega)
  · obtain ⟨d, rfl⟩ : ∃ d, t = M + d := ⟨t - M, by omega⟩
    exact down d

end CoefficientMass
