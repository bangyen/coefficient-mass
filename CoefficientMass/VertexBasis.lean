/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly

/-!
# A Basis at a Vertex

This module sets up Lemma 4.2 of `coefficient-mass-belowtwo.tex`.  For `y ∈ Z` put
`e_y(s) = s r_{Z \ {y}}(s)`.  Then `e_y(0) = 0`, `e_y` vanishes on `Z \ {y}`, `e_y(y) ≠ 0`, and
`deg e_y ≤ |Z|`; so a real `d` with `deg d ≤ |Z|`, `d(0) = 0` and `d|_S = 0` is
`∑_{y ∈ Z \ S} (d(y)/e_y(y)) e_y`, since the difference vanishes at the `|Z| + 1` points
`{0} ∪ Z`.

## Definitions

* `eY`.

## Theorems

* `eval_eY_zero`.
* `eval_eY_mem`.
* `eval_eY_self_ne`.
* `natDegree_eY_le`.
* `eq_sum_eY`.
-/

open Polynomial

namespace CoefficientMass

/-- `e_y(s) = s r_{Z \ {y}}(s)`. -/
noncomputable def eY (Z : Finset ℕ) (y : ℕ) : ℝ[X] :=
  X * confPolyP (Z.erase y)

theorem eval_eY_zero (Z : Finset ℕ) (y : ℕ) : (eY Z y).eval 0 = 0 := by
  rw [eY, eval_mul, eval_X, zero_mul]

theorem eval_eY_mem {Z : Finset ℕ} (h0 : 0 ∉ Z) {y z : ℕ} (hz : z ∈ Z) (hzy : z ≠ y) :
    (eY Z y).eval (z : ℝ) = 0 := by
  rw [eY, eval_mul, confPolyP_eval_mem (Finset.mem_erase.2 ⟨hzy, hz⟩)
    (fun h : z = 0 => h0 (h ▸ hz)), mul_zero]

theorem eval_eY_self_ne {Z : Finset ℕ} (h0 : 0 ∉ Z) {y : ℕ} (hy : y ∈ Z) :
    (eY Z y).eval (y : ℝ) ≠ 0 := by
  have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast fun h : y = 0 => h0 (h ▸ hy)
  rw [eY, eval_mul, eval_X, confPolyP, eval_prod]
  refine mul_ne_zero hy0 (Finset.prod_ne_zero_iff.2 fun z hz => ?_)
  obtain ⟨hzy, hzZ⟩ := Finset.mem_erase.1 hz
  have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast fun h : z = 0 => h0 (h ▸ hzZ)
  rw [eval_add, eval_mul, eval_C, eval_X, eval_C]
  intro h
  have : (y : ℝ) = z := by field_simp at h; linarith
  exact hzy (by exact_mod_cast this.symm)

theorem natDegree_eY_le {Z : Finset ℕ} {y : ℕ} (hy : y ∈ Z) : (eY Z y).natDegree ≤ Z.card := by
  rw [eY]
  refine natDegree_mul_le.trans ?_
  have := natDegree_confPolyP (Z.erase y)
  rw [Finset.card_erase_of_mem hy] at this
  have hc : 1 ≤ Z.card := Finset.card_pos.2 ⟨y, hy⟩
  have := natDegree_X_le (R := ℝ)
  omega

/-- A real `d` with `deg d ≤ |Z|`, `d(0) = 0` and `d|_S = 0` is
`∑_{y ∈ Z \ S} (d(y)/e_y(y)) e_y`. -/
theorem eq_sum_eY {S Z : Finset ℕ} (h0 : 0 ∉ Z) {d : ℝ[X]}
    (hd : d.natDegree ≤ Z.card) (hd0 : d.eval 0 = 0) (hdS : ∀ s ∈ S, d.eval (s : ℝ) = 0) :
    d = ∑ y ∈ Z \ S, C (d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)) * eY Z y := by
  set D := d - ∑ y ∈ Z \ S, C (d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)) * eY Z y
  have hsum_eval : ∀ x : ℝ, (∑ y ∈ Z \ S, C (d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)) *
      eY Z y).eval x = ∑ y ∈ Z \ S, d.eval (y : ℝ) / (eY Z y).eval (y : ℝ) * (eY Z y).eval x :=
    fun x => by rw [eval_finset_sum]; exact Finset.sum_congr rfl fun y _ => by rw [eval_mul, eval_C]
  have hDdeg : D.natDegree ≤ Z.card := by
    refine (natDegree_sub_le _ _).trans (max_le hd ?_)
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun y hy => ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_eY_le (Finset.mem_sdiff.1 hy).1)
  have hDZ : ∀ z ∈ Z, D.eval (z : ℝ) = 0 := fun z hz => by
    rw [eval_sub, hsum_eval]
    by_cases hzS : z ∈ S
    · rw [hdS z hzS, Finset.sum_eq_zero fun y hy => by
        rw [eval_eY_mem h0 hz fun h : z = y => (Finset.mem_sdiff.1 hy).2 (h ▸ hzS), mul_zero],
        sub_zero]
    · rw [Finset.sum_eq_single_of_mem z (Finset.mem_sdiff.2 ⟨hz, hzS⟩) fun y hy hyz => by
        rw [eval_eY_mem h0 hz (Ne.symm hyz), mul_zero],
        div_mul_cancel₀ _ (eval_eY_self_ne h0 hz), sub_self]
  have hD0 : D.eval 0 = 0 := by
    rw [eval_sub, hsum_eval, hd0, Finset.sum_eq_zero fun y _ => by rw [eval_eY_zero, mul_zero],
      sub_zero]
  have hDz : D = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D
      ((insert 0 Z).image (fun z : ℕ => (z : ℝ))) (fun x hx => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      rcases Finset.mem_insert.1 hz with rfl | hz
      · rw [Nat.cast_zero]
        exact hD0
      · exact hDZ z hz
    · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_insert_of_notMem h0]
      omega
  exact sub_eq_zero.1 hDz

end CoefficientMass
