/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.VertexNec
import CoefficientMass.SecondRowId

/-!
# `Φ_r` Along a Sign-Preserving Segment

This module collects the facts behind the existence claim of Lemma 6.11 of
`coefficient-mass-rows.tex`.  If `q(s)(q(s) + t d(s)) ≥ 0` for every `s ≥ 1` and `d` vanishes
wherever `q` does, then `Φ_r(q + t d) = Φ_r(q) + t ∑_s sgn(q(s)) d(s) r^{-s}`; and
`t Φ_r(d) ≤ Φ_r(q + t d) + Φ_r(q)` for `t ≥ 0`.

## Theorems

* `muR_le_adm`.
* `abs_line`.
* `rowPhi_add_line`.
* `mul_rowPhi_le`.
* `rowPhi_pos`.
* `sign_step`.
-/

open Polynomial

namespace CoefficientMass

/-- `μ_r(S, L) ≤ Φ_r(q)` for every admissible `q`. -/
theorem muR_le_adm {r : ℝ} {S : Finset ℕ} {L : ℕ} {q : ℝ[X]} (hq : q.degree < L)
    (hq0 : q.eval 0 = 1) (hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0) : muR r S L ≤ rowPhi r q := by
  unfold muR
  refine ciInf_le ⟨0, ?_⟩ (⟨q, hq, hq0, hqS⟩ :
    {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})
  rintro _ ⟨q, rfl⟩
  exact tsum_nonneg fun _ => by positivity

/-- `|a + tb| = |a| + t sgn(a) b` when `a(a + tb) ≥ 0` and `b = 0` if `a = 0`. -/
theorem abs_line {a b t : ℝ} (hab : a = 0 → b = 0) (h : 0 ≤ a * (a + t * b)) :
    |a + t * b| = |a| + t * (Real.sign a * b) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, abs_of_nonpos (by nlinarith)]
    ring
  · simp only [hab ha, ha, mul_zero, add_zero, abs_zero]
  · rw [Real.sign_of_pos ha, abs_of_pos ha, abs_of_nonneg (by nlinarith)]
    ring

/-- `Φ_r(q + t d) = Φ_r(q) + t ∑_s sgn(q(s)) d(s) r^{-s}` on a sign-preserving segment. -/
theorem rowPhi_add_line {r : ℝ} (hr : 1 < r) {q d : ℝ[X]}
    (hqd : ∀ k : ℕ, q.eval ((k + 1 : ℕ) : ℝ) = 0 → d.eval ((k + 1 : ℕ) : ℝ) = 0) {t : ℝ}
    (ht : ∀ k : ℕ, 0 ≤ q.eval ((k + 1 : ℕ) : ℝ) *
      (q.eval ((k + 1 : ℕ) : ℝ) + t * d.eval ((k + 1 : ℕ) : ℝ))) :
    rowPhi r (q + C t * d) = rowPhi r q + t * ∑' k : ℕ, Real.sign (q.eval ((k + 1 : ℕ) : ℝ)) *
      d.eval ((k + 1 : ℕ) : ℝ) * (1 / r) ^ (k + 1) := by
  have key : ∀ k : ℕ, |(q + C t * d).eval ((k + 1 : ℕ) : ℝ)| * (1 / r) ^ (k + 1) =
      |q.eval ((k + 1 : ℕ) : ℝ)| * (1 / r) ^ (k + 1) + t * (Real.sign (q.eval ((k + 1 : ℕ) : ℝ)) *
        d.eval ((k + 1 : ℕ) : ℝ) * (1 / r) ^ (k + 1)) := fun k => by
    rw [eval_add, eval_mul, eval_C, abs_line (hqd k) (ht k)]
    ring
  unfold rowPhi
  rw [tsum_congr key, (summable_rowPhi hr q).tsum_add ((summable_sign_mul hr q d).mul_left t),
    tsum_mul_left]

/-- `t Φ_r(d) ≤ Φ_r(q + t d) + Φ_r(q)` for `t ≥ 0`. -/
theorem mul_rowPhi_le {r : ℝ} (hr : 1 < r) (q d : ℝ[X]) {t : ℝ} (ht : 0 ≤ t) :
    t * rowPhi r d ≤ rowPhi r (q + C t * d) + rowPhi r q := by
  unfold rowPhi
  rw [← tsum_mul_left, ← (summable_rowPhi hr _).tsum_add (summable_rowPhi hr q)]
  refine Summable.tsum_le_tsum (fun k => ?_) ((summable_rowPhi hr d).mul_left t)
    ((summable_rowPhi hr _).add (summable_rowPhi hr q))
  rw [eval_add, eval_mul, eval_C, ← mul_assoc, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  set a := q.eval ((k + 1 : ℕ) : ℝ)
  set b := d.eval ((k + 1 : ℕ) : ℝ)
  have h : |t * b| = t * |b| := by rw [abs_mul, abs_of_nonneg ht]
  rw [← h]
  exact abs_le.2 ⟨by linarith [le_abs_self (a + t * b), neg_abs_le (a + t * b),
    le_abs_self a, neg_abs_le a], by linarith [le_abs_self (a + t * b),
      neg_abs_le (a + t * b), le_abs_self a, neg_abs_le a]⟩

theorem rowPhi_pos {r : ℝ} (hr : 1 < r) {d : ℝ[X]} (hd : d ≠ 0) : 0 < rowPhi r d := by
  obtain ⟨k, -, hk⟩ := exists_eval_ne hd 0
  exact (summable_rowPhi hr d).tsum_pos (fun _ => by positivity) k (by
    have := abs_pos.2 hk
    positivity)

/-- `a(b + e) ≥ 0` when `ab ≥ 0` and `|e| < |b|`. -/
theorem sign_step {a b e : ℝ} (hab : 0 ≤ a * b) (he : |e| < |b|) : 0 ≤ a * (b + e) := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have ha : a ≤ 0 := by
      by_contra h
      push_neg at h
      nlinarith
    rw [abs_of_neg hb] at he
    nlinarith [le_abs_self e]
  · rw [hb, abs_zero] at he
    linarith [abs_nonneg e]
  · have ha : 0 ≤ a := by
      by_contra h
      push_neg at h
      nlinarith
    rw [abs_of_pos hb] at he
    nlinarith [neg_abs_le e]

end CoefficientMass
