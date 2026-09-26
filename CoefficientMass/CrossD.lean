/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.CrossRows
import CoefficientMass.OptIns

/-!
# Crossing for Truncated Sums

The proof of Theorem 4.3 of `coefficient-mass-rows.tex` uses only the pointwise inequality
`|λ q_1(s) + (1 - λ) q_2(s)| ≤ λ |q_1(s)| + (1 - λ) |q_2(s)|` of Lemma 4.1(a), so it applies to
the truncated sums `Φ_{r,D}`; this is the form used in the proof of Theorem 5.3.

## Theorems

* `exists_combo_zero`.
* `phiD_combo_le`.
* `muRD_le_of_sign`.
* `muRD_insert_le`.
-/

open Polynomial

namespace CoefficientMass

/-- If `a b ≤ 0`, some `0 ≤ λ ≤ 1` has `λ a + (1 - λ) b = 0`. -/
theorem exists_combo_zero {a b : ℝ} (h : a * b ≤ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t * a + (1 - t) * b = 0 := by
  by_cases hab : a = b
  · have ha : a = 0 := by
      subst hab
      exact mul_self_eq_zero.1 (le_antisymm h (mul_self_nonneg a))
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [← hab, ha]
    ring
  · have hne : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    refine ⟨b / (b - a), ?_, ?_, ?_⟩
    · rcases hne.lt_or_gt with hlt | hgt
      · exact div_nonneg_of_nonpos (by nlinarith) hlt.le
      · exact div_nonneg (by nlinarith) hgt.le
    · rcases hne.lt_or_gt with hlt | hgt
      · rw [div_le_one_of_neg hlt]
        nlinarith
      · rw [div_le_one hgt]
        nlinarith
    · have hbt : b / (b - a) * (b - a) = b := div_mul_cancel₀ b hne
      linear_combination -hbt

/-- `Φ_{r,D}(λ p + (1 - λ) q) ≤ λ Φ_{r,D}(p) + (1 - λ) Φ_{r,D}(q)` for `0 ≤ λ ≤ 1`. -/
theorem phiD_combo_le {r : ℝ} (hr : 1 < r) (D : ℕ) (p q : ℝ[X]) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    phiD r D (C t * p + C (1 - t) * q) ≤ t * phiD r D p + (1 - t) * phiD r D q := by
  rw [phiD, phiD, phiD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [eval_add, eval_mul, eval_mul, eval_C, eval_C]
  have h := abs_add_le (t * p.eval (s : ℝ)) ((1 - t) * q.eval (s : ℝ))
  rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)] at h
  have hxd : 0 ≤ (1 / r) ^ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h hxd]

/-- Lemma 4.1(a) of `coefficient-mass-rows.tex` for `Φ_{r,D}`: two admissible `q_1, q_2` with
`Φ_{r,D}(q_i) ≤ φ` and `q_1(σ) q_2(σ) ≤ 0` give `μ_{r,D}(T ∪ {σ}, L) ≤ φ`. -/
theorem muRD_le_of_sign {r : ℝ} (hr : 1 < r) (D L : ℕ) {φ : ℝ} (T : Finset ℕ) (σ : ℕ)
    {q₁ q₂ : ℝ[X]} (hq₁ : q₁.degree < L) (hq₂ : q₂.degree < L) (h₁0 : q₁.eval 0 = 1)
    (h₂0 : q₂.eval 0 = 1) (h₁T : ∀ s ∈ T, q₁.eval (s : ℝ) = 0)
    (h₂T : ∀ s ∈ T, q₂.eval (s : ℝ) = 0) (hΦ₁ : phiD r D q₁ ≤ φ) (hΦ₂ : phiD r D q₂ ≤ φ)
    (hsign : q₁.eval (σ : ℝ) * q₂.eval (σ : ℝ) ≤ 0) : muRD r D (insert σ T) L ≤ φ := by
  obtain ⟨t, ht0, ht1, ht⟩ := exists_combo_zero hsign
  have hq : (C t * q₁ + C (1 - t) * q₂).degree < L := by
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt hq₁
    · rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt hq₂
  have hq0 : (C t * q₁ + C (1 - t) * q₂).eval 0 = 1 := by
    rw [eval_add, eval_mul, eval_mul, eval_C, eval_C, h₁0, h₂0]
    ring
  have hqS : ∀ s ∈ insert σ T, (C t * q₁ + C (1 - t) * q₂).eval (s : ℝ) = 0 := fun s hs => by
    rw [eval_add, eval_mul, eval_mul, eval_C, eval_C]
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ht
    · rw [h₁T s hs, h₂T s hs]
      ring
  refine (ciInf_le ⟨0, by
    rintro _ ⟨q', rfl⟩
    exact Finset.sum_nonneg fun _ _ => by positivity⟩
    (⟨_, hq, hq0, hqS⟩ :
      {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ insert σ T, q.eval (s : ℝ) = 0})).trans
    ((phiD_combo_le hr D q₁ q₂ ht0 ht1).trans ?_)
  nlinarith

/-- Theorem 4.3 of `coefficient-mass-rows.tex` for `Φ_{r,D}`: with `h = h_t(W)`,
`μ_{r,D}(T ∪ {σ}, |W| + 2) ≤ max(Φ_{r,D}(r_W), Φ_{r,D}(r_{ins(W, h)}))` for `σ > t`. -/
theorem muRD_insert_le {r : ℝ} (hr : 1 < r) (D t : ℕ) (W T : Finset ℕ) (σ : ℕ) (h0 : 0 ∉ W)
    (hTW : T ⊆ W) (hTt : ∀ x ∈ T, x ≤ t) (hσ : t < σ) :
    muRD r D (insert σ T) (W.card + 2) ≤
      max (phiD r D (confPolyP W)) (phiD r D (confPolyP (ins W (firstGap t W)))) := by
  classical
  obtain ⟨hth, hhW, hbelow⟩ := firstGap_spec t W
  set h := firstGap t W
  obtain ⟨hlow, hhW', hcard, hflip⟩ := insFlip W h h0 (by omega) hhW
  have h0' : 0 ∉ ins W h := fun hz => by
    have : (0 : ℕ) ∈ (ins W h).filter (· < h) := Finset.mem_filter.2 ⟨hz, by omega⟩
    rw [hlow] at this
    exact h0 (Finset.mem_filter.1 this).1
  have hadm₁ := confPolyP_admissible (L := W.card + 2) h0 (by omega)
  have hadm₂ := confPolyP_admissible (L := W.card + 2) h0' (by rw [hcard]; omega)
  have hTW' : T ⊆ ins W h := fun x hx => by
    have : x ∈ (ins W h).filter (· < h) := by
      rw [hlow]
      exact Finset.mem_filter.2 ⟨hTW hx, by have := hTt x hx; omega⟩
    exact (Finset.mem_filter.1 this).1
  have hsign : (confPolyP W).eval (σ : ℝ) * (confPolyP (ins W h)).eval (σ : ℝ) ≤ 0 := by
    rcases lt_trichotomy σ h with hσh | hσh | hσh
    · rw [confPolyP_eval_mem (hbelow σ hσ hσh) (by omega), zero_mul]
    · rw [hσh, confPolyP_eval_mem hhW' (by omega), mul_zero]
    · by_cases hσW : σ ∈ W
      · rw [confPolyP_eval_mem hσW (by omega), zero_mul]
      by_cases hσW' : σ ∈ ins W h
      · rw [confPolyP_eval_mem hσW' (by omega), mul_zero]
      have := hflip σ hσh hσW hσW'
      rw [confPoly_eq_eval, confPoly_eq_eval] at this
      exact this.le
  exact muRD_le_of_sign hr D (W.card + 2) T σ hadm₁.1 hadm₂.1 hadm₁.2.1 hadm₂.2.1
    (fun s hs => hadm₁.2.2 s (hTW hs)) (fun s hs => hadm₂.2.2 s (hTW' hs)) (le_max_left _ _)
    (le_max_right _ _) hsign

end CoefficientMass
