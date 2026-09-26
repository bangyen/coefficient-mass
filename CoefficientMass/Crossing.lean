/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowLast

/-!
# Crossing

This module proves Lemma 4.1 of `coefficient-mass-rows.tex`.  `Φ_r` is convex, so if two
admissible polynomials take values of opposite signs at `σ`, the combination vanishing at
`σ` is admissible for `μ_r(T ∪ {σ}, L)` with `Φ_r` at most the larger of the two; and
`1 - s/σ'` is a convex combination of `1` and `1 - s/y` for `0 < y ≤ σ'`.

## Definitions

* `Crossing`.

## Theorems

* `rowPhi_combo_le`.
* `crossing`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 4.1 of `coefficient-mass-rows.tex`.  (a) If `q_1, q_2` are real with
`deg q_i < L`, `q_i(0) = 1`, `q_i|_T = 0`, `Φ_r(q_i) ≤ φ` and `q_1(σ) q_2(σ) ≤ 0` for
`σ ∈ ℕ_{>0} \ T`, then `|T| + 1 < L` and `μ_r(T ∪ {σ}, L) ≤ φ`.  (b) For real `Q` and
`0 < y ≤ σ'`, `Φ_r(Q (1 - s/σ')) ≤ max(Φ_r(Q), Φ_r(Q (1 - s/y)))`. -/
def Crossing : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ (L : ℕ) (φ : ℝ) (T : Finset ℕ) (σ : ℕ) (q₁ q₂ : ℝ[X]), 0 ∉ T → 0 < σ → σ ∉ T →
      q₁.degree < L → q₂.degree < L → q₁.eval 0 = 1 → q₂.eval 0 = 1 →
      (∀ s ∈ T, q₁.eval (s : ℝ) = 0) → (∀ s ∈ T, q₂.eval (s : ℝ) = 0) →
      rowPhi r q₁ ≤ φ → rowPhi r q₂ ≤ φ → q₁.eval (σ : ℝ) * q₂.eval (σ : ℝ) ≤ 0 →
        T.card + 1 < L ∧ muR r (insert σ T) L ≤ φ) ∧
    ∀ (Q : ℝ[X]) (y σ' : ℝ), 0 < y → y ≤ σ' →
      rowPhi r (Q * (1 - C (1 / σ') * X)) ≤
        max (rowPhi r Q) (rowPhi r (Q * (1 - C (1 / y) * X)))

/-- `Φ_r(λ p + (1 - λ) q) ≤ λ Φ_r(p) + (1 - λ) Φ_r(q)` for `0 ≤ λ ≤ 1`. -/
theorem rowPhi_combo_le {r : ℝ} (hr : 1 < r) (p q : ℝ[X]) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rowPhi r (C t * p + C (1 - t) * q) ≤ t * rowPhi r p + (1 - t) * rowPhi r q := by
  have hx : 0 < 1 / r := by positivity
  rw [rowPhi, rowPhi, rowPhi, ← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_rowPhi hr p).mul_left t).tsum_add ((summable_rowPhi hr q).mul_left (1 - t))]
  refine Summable.tsum_le_tsum (fun d => ?_) (summable_rowPhi hr _)
    (((summable_rowPhi hr p).mul_left t).add ((summable_rowPhi hr q).mul_left (1 - t)))
  rw [eval_add, eval_mul, eval_mul, eval_C, eval_C]
  have h := abs_add_le (t * p.eval ((d + 1 : ℕ) : ℝ)) ((1 - t) * q.eval ((d + 1 : ℕ) : ℝ))
  rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg (by linarith)] at h
  have hxd : 0 ≤ (1 / r) ^ (d + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h hxd]

theorem crossing : Crossing := by
  intro r hr
  refine ⟨fun L φ T σ q₁ q₂ hT0 hσ hσT hq₁ hq₂ h₁0 h₂0 h₁T h₂T hΦ₁ hΦ₂ hsign => ?_,
    fun Q y σ' hy hyσ => ?_⟩
  · -- a combination vanishing at `σ`
    obtain ⟨q, hq, hq0, hqT, hqσ, hΦ⟩ : ∃ q : ℝ[X], q.degree < L ∧ q.eval 0 = 1 ∧
        (∀ s ∈ T, q.eval (s : ℝ) = 0) ∧ q.eval (σ : ℝ) = 0 ∧ rowPhi r q ≤ φ := by
      by_cases h₁ : q₁.eval (σ : ℝ) = 0
      · exact ⟨q₁, hq₁, h₁0, h₁T, h₁, hΦ₁⟩
      by_cases h₂ : q₂.eval (σ : ℝ) = 0
      · exact ⟨q₂, hq₂, h₂0, h₂T, h₂, hΦ₂⟩
      set a := q₁.eval (σ : ℝ)
      set b := q₂.eval (σ : ℝ)
      have hab : a * b < 0 := lt_of_le_of_ne hsign (mul_ne_zero h₁ h₂)
      have hba : b - a ≠ 0 := fun h => by
        rw [sub_eq_zero] at h
        rw [h] at hab
        nlinarith
      set t := b / (b - a)
      have ht0 : 0 ≤ t := by
        rcases lt_or_gt_of_ne h₂ with hb | hb
        · have : a > 0 := by nlinarith
          exact div_nonneg_of_nonpos hb.le (by linarith)
        · have : a < 0 := by nlinarith
          exact div_nonneg hb.le (by linarith)
      have ht1 : t ≤ 1 := by
        rcases lt_or_gt_of_ne h₂ with hb | hb
        · have : a > 0 := by nlinarith
          rw [div_le_one_of_neg (by linarith)]
          linarith
        · have : a < 0 := by nlinarith
          rw [div_le_one (by linarith)]
          linarith
      refine ⟨C t * q₁ + C (1 - t) * q₂, ?_, ?_, fun s hs => ?_, ?_, ?_⟩
      · refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · rw [← smul_eq_C_mul]
          exact (degree_smul_le _ _).trans_lt hq₁
        · rw [← smul_eq_C_mul]
          exact (degree_smul_le _ _).trans_lt hq₂
      · rw [eval_add, eval_mul, eval_mul, eval_C, eval_C, h₁0, h₂0]
        ring
      · rw [eval_add, eval_mul, eval_mul, h₁T s hs, h₂T s hs]
        ring
      · rw [eval_add, eval_mul, eval_mul, eval_C, eval_C]
        change t * a + (1 - t) * b = 0
        have hbt : t * (b - a) = b := div_mul_cancel₀ b hba
        linear_combination -hbt
      · refine (rowPhi_combo_le hr q₁ q₂ ht0 ht1).trans ?_
        nlinarith
    -- its zeros bound the size of `T`
    have hne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
    have hcard : T.card + 1 < L := by
      have hroots := Polynomial.card_roots' q
      have hsub : ((insert σ T).image fun s : ℕ => (s : ℝ)).val ≤ q.roots := by
        rw [Finset.val_le_iff_val_subset]
        intro x hx
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
        refine (mem_roots hne).2 ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact hqσ
        · exact hqT s hs
      have h1 := (Multiset.card_le_card hsub).trans hroots
      rw [Finset.card_val, Finset.card_image_of_injective _ Nat.cast_injective,
        Finset.card_insert_of_notMem hσT] at h1
      have h2 : q.natDegree < L := by
        rw [degree_eq_natDegree hne] at hq
        exact_mod_cast hq
      omega
    refine ⟨hcard, ?_⟩
    have hins0 : 0 ∉ insert σ T := fun h => by
      rcases Finset.mem_insert.1 h with h | h
      · omega
      · exact hT0 h
    refine (ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by
        have : 0 < 1 / r := by positivity
        positivity⟩
      (⟨q, hq, hq0, fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact hqσ
        · exact hqT s hs⟩ : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧
          ∀ s ∈ insert σ T, q.eval (s : ℝ) = 0})).trans hΦ
  · -- `1 - s/σ' = (1 - λ) + λ (1 - s/y)` with `λ = y/σ'`
    have hσ' : 0 < σ' := lt_of_lt_of_le hy hyσ
    set t := y / σ'
    have ht0 : 0 ≤ t := div_nonneg hy.le hσ'.le
    have ht1 : t ≤ 1 := by rw [div_le_one hσ']; exact hyσ
    have hy0 : y ≠ 0 := hy.ne'
    have hσ0 : σ' ≠ 0 := hσ'.ne'
    have key : t * (1 / y) = 1 / σ' := by
      simp only [t]
      rw [div_mul_div_comm, mul_one, div_eq_div_iff (mul_ne_zero hσ0 hy0) hσ0]
      ring
    have hcombo : Q * (1 - C (1 / σ') * X) =
        C t * (Q * (1 - C (1 / y) * X)) + C (1 - t) * Q := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X]
      rw [← key]
      ring
    rw [hcombo]
    refine (rowPhi_combo_le hr _ _ ht0 ht1).trans ?_
    have h1 := le_max_left (rowPhi r Q) (rowPhi r (Q * (1 - C (1 / y) * X)))
    have h2 := le_max_right (rowPhi r Q) (rowPhi r (Q * (1 - C (1 / y) * X)))
    nlinarith

end CoefficientMass
