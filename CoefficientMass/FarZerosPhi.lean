/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.SecondRowId
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Far-Zero Weight `φ_m`

This module sets up Lemma 6.18 of `coefficient-mass-rows.tex`.  For `t > 0` put
`φ_m(s, t) = -s` for `s ≤ t` and `(s - t)(s/t)^{m-1} - t` for `s > t`, and
`Δ_{q,m}(t) = ∑_{s ≥ 1} φ_m(s, t) |q(s)| r^{-s}`.  Then `|φ_m(s, t)| ≤ 2c(1 + s)^m` with
`c = max(1, 1/t)^{m-1}`, `φ_m(s, ·)` does not increase, `φ_m ≤ φ_{m+1}`, and `φ_m(s, t) = -s`
once `t ≥ s`; dominated convergence gives `Δ_{q,m}(t) → -Ψ_r(q)`.

## Definitions

* `phiM`.
* `deltaQ`.

## Theorems

* `abs_phiM_le`.
* `phiM_anti`.
* `phiM_le_succ`.
* `abs_eval_one_add_pow`.
* `summable_deltaQ`.
* `deltaQ_anti`.
* `deltaQ_le_succ`.
* `tendsto_deltaQ`.
* `deltaQ_one`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `φ_m(s, t) = -s` for `s ≤ t` and `(s - t)(s/t)^{m-1} - t` for `s > t`. -/
noncomputable def phiM (m s : ℕ) (t : ℝ) : ℝ :=
  if (s : ℝ) ≤ t then -(s : ℝ) else ((s : ℝ) - t) * ((s : ℝ) / t) ^ (m - 1) - t

/-- `Δ_{q,m}(t) = ∑_{s ≥ 1} φ_m(s, t) |q(s)| r^{-s}`. -/
noncomputable def deltaQ (r : ℝ) (q : ℝ[X]) (m : ℕ) (t : ℝ) : ℝ :=
  ∑' d : ℕ, phiM m (d + 1) t * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)

theorem abs_phiM_le {m : ℕ} (hm : 1 ≤ m) (s : ℕ) {t : ℝ} (ht : 0 < t) :
    |phiM m s t| ≤ 2 * max 1 (1 / t) ^ (m - 1) * (1 + (s : ℝ)) ^ m := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hc : 1 ≤ max 1 (1 / t) ^ (m - 1) := one_le_pow₀ (le_max_left _ _)
  have h1 : (s : ℝ) ≤ (1 + (s : ℝ)) ^ m :=
    (by linarith : (s : ℝ) ≤ 1 + s).trans (le_self_pow₀ (by linarith) (by omega))
  have hpow0 : (0 : ℝ) ≤ (1 + (s : ℝ)) ^ m := by positivity
  unfold phiM
  split_ifs with h
  · rw [abs_neg, abs_of_nonneg hs0]
    nlinarith
  · push_neg at h
    have hst : (0 : ℝ) ≤ (s : ℝ) - t := by linarith
    have hq : (s : ℝ) / t ≤ s * max 1 (1 / t) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hs0
    have ha : ((s : ℝ) - t) * ((s : ℝ) / t) ^ (m - 1) ≤
        max 1 (1 / t) ^ (m - 1) * (1 + (s : ℝ)) ^ m := by
      calc ((s : ℝ) - t) * ((s : ℝ) / t) ^ (m - 1)
          ≤ (s : ℝ) * ((s : ℝ) * max 1 (1 / t)) ^ (m - 1) :=
            mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hq _) (by positivity) hs0
        _ = max 1 (1 / t) ^ (m - 1) * (s : ℝ) ^ m := by
            rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]
            ring
        _ ≤ max 1 (1 / t) ^ (m - 1) * (1 + (s : ℝ)) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 (by linarith) m) (by positivity)
    have ha0 : 0 ≤ ((s : ℝ) - t) * ((s : ℝ) / t) ^ (m - 1) := mul_nonneg hst (by positivity)
    rw [abs_le]
    constructor <;> nlinarith

theorem phiM_anti (m s : ℕ) {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') :
    phiM m s t' ≤ phiM m s t := by
  unfold phiM
  split_ifs with h1 h2 h2
  · exact le_rfl
  · push_neg at h2
    have : 0 ≤ ((s : ℝ) - t) * ((s : ℝ) / t) ^ (m - 1) :=
      mul_nonneg (by linarith) (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; positivity)
    linarith
  · linarith
  · push_neg at h1 h2
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hq : (s : ℝ) / t' ≤ s / t := div_le_div_of_nonneg_left hs0 ht h
    have ht' : 0 < t' := ht.trans_le h
    have := mul_le_mul (by linarith : (s : ℝ) - t' ≤ s - t)
      (pow_le_pow_left₀ (div_nonneg hs0 ht'.le) hq (m - 1))
      (pow_nonneg (div_nonneg hs0 ht'.le) _) (by linarith)
    linarith

theorem phiM_le_succ (m s : ℕ) {t : ℝ} (ht : 0 < t) : phiM m s t ≤ phiM (m + 1) s t := by
  unfold phiM
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    rw [Nat.add_sub_cancel]
    have h1 : 1 ≤ (s : ℝ) / t := by rw [le_div_iff₀ ht]; linarith
    have := pow_le_pow_right₀ h1 (show m - 1 ≤ m by omega)
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ s - t)
    linarith

/-- `(1 + y)^m |q(y)| = |((1 + X)^m q)(y)|` for `y ≥ 0`. -/
theorem abs_eval_one_add_pow (q : ℝ[X]) (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ m * |q.eval y| = |((1 + X) ^ m * q).eval y| := by
  rw [eval_mul, eval_pow, eval_add, eval_one, eval_X, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + y)]

theorem summable_deltaQ {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) (q : ℝ[X]) {t : ℝ}
    (ht : 0 < t) :
    Summable fun d : ℕ => phiM m (d + 1) t * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by
  refine Summable.of_norm_bounded
    ((summable_rowPhi hr ((1 + X) ^ m * q)).mul_left (2 * max 1 (1 / t) ^ (m - 1))) fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (1 / r) ^ (d + 1)),
    ← abs_eval_one_add_pow q m (Nat.cast_nonneg _)]
  have := abs_phiM_le hm (d + 1) ht
  calc |phiM m (d + 1) t| * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
      ≤ 2 * max 1 (1 / t) ^ (m - 1) * (1 + ((d + 1 : ℕ) : ℝ)) ^ m *
          |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (by positivity)
    _ = _ := by ring

theorem deltaQ_anti {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) (q : ℝ[X]) {t t' : ℝ}
    (ht : 0 < t) (h : t ≤ t') : deltaQ r q m t' ≤ deltaQ r q m t :=
  Summable.tsum_le_tsum (fun _ => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (phiM_anti m _ ht h) (abs_nonneg _)) (by positivity))
    (summable_deltaQ hr hm q (ht.trans_le h)) (summable_deltaQ hr hm q ht)

theorem deltaQ_le_succ {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) (q : ℝ[X]) {t : ℝ}
    (ht : 0 < t) : deltaQ r q m t ≤ deltaQ r q (m + 1) t :=
  Summable.tsum_le_tsum (fun _ => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (phiM_le_succ m _ ht) (abs_nonneg _)) (by positivity))
    (summable_deltaQ hr hm q ht) (summable_deltaQ hr (by omega) q ht)

/-- `Δ_{q,m}(t) → -Ψ_r(q)` as `t → ∞`. -/
theorem tendsto_deltaQ {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) (q : ℝ[X]) :
    Tendsto (deltaQ r q m) atTop (𝓝 (-psiR r q)) := by
  have hsum : Summable fun d : ℕ =>
      2 * (|((1 + X) ^ m * q).eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) :=
    (summable_rowPhi hr ((1 + X) ^ m * q)).mul_left 2
  have hlim : ∀ d : ℕ, Tendsto (fun t : ℝ => phiM m (d + 1) t * |q.eval ((d + 1 : ℕ) : ℝ)| *
      (1 / r) ^ (d + 1)) atTop
      (𝓝 (-(((d + 1 : ℕ) : ℝ) * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)))) := fun d =>
    tendsto_nhds_of_eventually_eq ((eventually_ge_atTop (((d + 1 : ℕ) : ℝ))).mono
      fun t ht => by rw [phiM, if_pos ht]; ring)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ d : ℕ,
      ‖phiM m (d + 1) t * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)‖ ≤
        2 * (|((1 + X) ^ m * q).eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) := by
    refine (eventually_ge_atTop 1).mono fun t ht d => ?_
    have hb := abs_phiM_le hm (d + 1) (by linarith : (0 : ℝ) < t)
    rw [max_eq_left (by rw [div_le_one (by linarith)]; exact ht), one_pow, mul_one] at hb
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (1 / r) ^ (d + 1)),
      ← abs_eval_one_add_pow q m (Nat.cast_nonneg _)]
    calc |phiM m (d + 1) t| * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
        ≤ 2 * (1 + ((d + 1 : ℕ) : ℝ)) ^ m * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) (by positivity)
      _ = _ := by ring
  have h := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  rw [tsum_neg] at h
  exact h

/-- `Δ_{q,1}(σ) = 2R_q(σ) - Ψ_r(q)`. -/
theorem deltaQ_one {r : ℝ} (hr : 1 < r) (q : ℝ[X]) {σ : ℝ} (hσ : 0 < σ) :
    deltaQ r q 1 σ = 2 * remR r q σ - psiR r q := by
  have key : ∀ d : ℕ, phiM 1 (d + 1) σ * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) =
      2 * (max (((d + 1 : ℕ) : ℝ) - σ) 0 * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) -
        ((d + 1 : ℕ) : ℝ) * |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := fun d => by
    unfold phiM
    split_ifs with h
    · rw [max_eq_right (by linarith)]
      ring
    · push_neg at h
      rw [max_eq_left (by linarith), Nat.sub_self, pow_zero]
      ring
  unfold deltaQ
  rw [tsum_congr key, ((summable_remR hr q hσ.le).mul_left 2).tsum_sub (summable_psiR hr q),
    tsum_mul_left]
  rfl

end CoefficientMass
