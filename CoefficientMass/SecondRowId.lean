/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly

/-!
# One Far Zero

This module proves the identity before Lemma 6.11 of `coefficient-mass-rows.tex`: with
`Ψ_r(p) = ∑_{s ≥ 1} s |p(s)| r^{-s}` and `R_p(σ) = ∑_{s > σ} (s - σ) |p(s)| r^{-s}`,
`|1 - s/σ| = 1 - s/σ + 2(s/σ - 1)^+` gives
`Φ_r((1 - s/σ) p) = Φ_r(p) - (Ψ_r(p) - 2R_p(σ))/σ`.  For `p ≠ 0`, `Ψ_r(p) > 0`,
`R_p(σ + 1) < R_p(σ)`, and `R_p(σ) → 0`, so some least integer `σ_* ≥ 1` has
`2R_p(σ_*) ≤ Ψ_r(p)`.

## Definitions

* `psiR`.
* `remR`.

## Theorems

* `summable_psiR`.
* `summable_remR`.
* `rowPhi_mul_lin`.
* `exists_eval_ne`.
* `psiR_pos`.
* `remR_anti`.
* `remR_succ_lt`.
* `exists_remR_lt`.
* `exists_sigma_star`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `Ψ_r(p) = ∑_{s ≥ 1} s |p(s)| r^{-s}`. -/
noncomputable def psiR (r : ℝ) (p : ℝ[X]) : ℝ :=
  ∑' d : ℕ, ((d + 1 : ℕ) : ℝ) * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)

/-- `R_p(σ) = ∑_{s > σ} (s - σ) |p(s)| r^{-s}`. -/
noncomputable def remR (r : ℝ) (p : ℝ[X]) (σ : ℝ) : ℝ :=
  ∑' d : ℕ, max (((d + 1 : ℕ) : ℝ) - σ) 0 * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)

theorem summable_psiR {r : ℝ} (hr : 1 < r) (p : ℝ[X]) :
    Summable fun d : ℕ => ((d + 1 : ℕ) : ℝ) * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
  (summable_rowPhi hr (X * p)).congr fun d => by
    rw [eval_mul, eval_X, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

theorem summable_remR {r : ℝ} (hr : 1 < r) (p : ℝ[X]) {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable fun d : ℕ =>
      max (((d + 1 : ℕ) : ℝ) - σ) 0 * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
  Summable.of_nonneg_of_le
    (fun d => mul_nonneg (mul_nonneg (le_max_right _ _) (abs_nonneg _)) (by positivity))
    (fun d => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (max_le (by linarith) (Nat.cast_nonneg _)) (abs_nonneg _)) (by positivity))
    (summable_psiR hr p)

/-- `Φ_r(p (1 - s/σ)) = Φ_r(p) - (Ψ_r(p) - 2R_p(σ))/σ` for `σ > 0`. -/
theorem rowPhi_mul_lin {r : ℝ} (hr : 1 < r) (p : ℝ[X]) {σ : ℝ} (hσ : 0 < σ) :
    rowPhi r (p * (1 - C (1 / σ) * X)) = rowPhi r p - (psiR r p - 2 * remR r p σ) / σ := by
  have key : ∀ d : ℕ, |(p * (1 - C (1 / σ) * X)).eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) =
      |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) -
        1 / σ * (((d + 1 : ℕ) : ℝ) * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) +
        2 / σ * (max (((d + 1 : ℕ) : ℝ) - σ) 0 * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) :=
    fun d => by
      rw [eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X, abs_mul]
      have e : |1 - 1 / σ * ((d + 1 : ℕ) : ℝ)| =
          1 - 1 / σ * ((d + 1 : ℕ) : ℝ) + 2 / σ * max (((d + 1 : ℕ) : ℝ) - σ) 0 := by
        rcases le_total (((d + 1 : ℕ) : ℝ)) σ with h | h
        · rw [max_eq_right (by linarith), abs_of_nonneg (by
            rw [sub_nonneg, one_div_mul_eq_div, div_le_one hσ]
            exact h)]
          ring
        · rw [max_eq_left (by linarith), abs_of_nonpos (by
            rw [sub_nonpos, one_div_mul_eq_div, one_le_div hσ]
            exact h)]
          field_simp
          ring
      rw [e]
      ring
  unfold rowPhi psiR remR
  rw [tsum_congr key, ((summable_rowPhi hr p).sub ((summable_psiR hr p).mul_left _)).tsum_add
    ((summable_remR hr p hσ.le).mul_left _), (summable_rowPhi hr p).tsum_sub
    ((summable_psiR hr p).mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- A nonzero `p` has `p(d + 1) ≠ 0` for some `d ≥ N`. -/
theorem exists_eval_ne {p : ℝ[X]} (hp : p ≠ 0) (N : ℕ) :
    ∃ d, N ≤ d ∧ p.eval ((d + 1 : ℕ) : ℝ) ≠ 0 := by
  by_contra h
  push_neg at h
  refine hp (p.eq_zero_of_infinite_isRoot (Set.infinite_of_injective_forall_mem
    (f := fun d : ℕ => ((N + d + 1 : ℕ) : ℝ)) (fun a b hab => ?_) fun d => h (N + d) (by omega)))
  have : ((N + a + 1 : ℕ) : ℝ) = ((N + b + 1 : ℕ) : ℝ) := hab
  have := Nat.cast_injective this
  omega

theorem psiR_pos {r : ℝ} (hr : 1 < r) {p : ℝ[X]} (hp : p ≠ 0) : 0 < psiR r p := by
  obtain ⟨d, -, hd⟩ := exists_eval_ne hp 0
  exact (summable_psiR hr p).tsum_pos (fun _ => by positivity) d (by
    have := abs_pos.2 hd
    positivity)

/-- `R_p` does not increase. -/
theorem remR_anti {r : ℝ} (hr : 1 < r) (p : ℝ[X]) {σ σ' : ℝ} (hσ : 0 ≤ σ) (h : σ ≤ σ') :
    remR r p σ' ≤ remR r p σ :=
  Summable.tsum_le_tsum (fun d => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (max_le_max (by linarith) le_rfl) (abs_nonneg _)) (by positivity))
    (summable_remR hr p (hσ.trans h)) (summable_remR hr p hσ)

/-- `R_p(σ + 1) < R_p(σ)` for `p ≠ 0` and integers `σ ≥ 0`. -/
theorem remR_succ_lt {r : ℝ} (hr : 1 < r) {p : ℝ[X]} (hp : p ≠ 0) (σ : ℕ) :
    remR r p ((σ + 1 : ℕ) : ℝ) < remR r p (σ : ℝ) := by
  obtain ⟨d, hd, hne⟩ := exists_eval_ne hp σ
  refine Summable.tsum_lt_tsum (i := d) (fun e => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (max_le_max (by push_cast; linarith) le_rfl) (abs_nonneg _))
    (by positivity)) ?_ (summable_remR hr p (Nat.cast_nonneg _))
    (summable_remR hr p (Nat.cast_nonneg _))
  have hpos : 0 < |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
    mul_pos (abs_pos.2 hne) (by positivity)
  have h1 : max (((d + 1 : ℕ) : ℝ) - ((σ + 1 : ℕ) : ℝ)) 0 < max (((d + 1 : ℕ) : ℝ) - σ) 0 := by
    have : (σ : ℝ) + 1 ≤ d + 1 := by exact_mod_cast Nat.succ_le_succ hd
    rw [max_eq_left (by push_cast; linarith : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) - ((σ + 1 : ℕ) : ℝ)),
      max_eq_left (by push_cast; linarith)]
    push_cast
    linarith
  rw [mul_assoc, mul_assoc]
  exact mul_lt_mul_of_pos_right h1 hpos

/-- `R_p(N) → 0`: for `ε > 0` some integer `N` has `R_p(N) < ε`. -/
theorem exists_remR_lt {r : ℝ} (hr : 1 < r) (p : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, remR r p N < ε := by
  set f : ℕ → ℝ := fun d => ((d + 1 : ℕ) : ℝ) * |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_sum_nat_add f).eventually (gt_mem_nhds hε))
  refine ⟨N, lt_of_le_of_lt ?_ (hN N le_rfl)⟩
  have hs := summable_remR hr p (Nat.cast_nonneg N)
  rw [remR, ← hs.sum_add_tsum_nat_add N, Finset.sum_eq_zero fun d hd => by
    have : ((d + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.1 hd
    rw [max_eq_right (by linarith), zero_mul, zero_mul], zero_add]
  refine Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (max_le (by linarith [Nat.cast_nonneg (α := ℝ) N]) (Nat.cast_nonneg _)) (abs_nonneg _))
    (by positivity)) ((summable_nat_add_iff N).2 hs) ((summable_nat_add_iff N).2
    (summable_psiR hr p))

/-- For `p ≠ 0` some integer `σ ≥ 1` has `2R_p(σ) ≤ Ψ_r(p)`. -/
theorem exists_sigma_star {r : ℝ} (hr : 1 < r) {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ σ : ℕ, 1 ≤ σ ∧ 2 * remR r p σ ≤ psiR r p := by
  obtain ⟨N, hN⟩ := exists_remR_lt hr p (half_pos (psiR_pos hr hp))
  refine ⟨N + 1, by omega, ?_⟩
  have := remR_anti hr p (Nat.cast_nonneg N)
    (show (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by push_cast; linarith)
  linarith

end CoefficientMass
