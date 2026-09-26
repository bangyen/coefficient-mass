/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Defs
import CoefficientMass.QuadRolle

/-!
# The Reciprocal Polynomial

This module starts the proof of Proposition 4.2 of `coefficient-mass.tex`.  The
reciprocal `F^*(t) = t^D F(1/t)` of a multiple `F` of `∏ (x - r_i)` is a multiple of
`∏ (1 - r_i t) = ∏ (-r_i) · ∏ (t - 1/r_i)`, so for `r_i ≥ 2` it has at least `L` zeros in
`(0, 1/2]`, counted with multiplicity.

## Theorems

* `reverse_prod_fin`.
* `reverse_X_sub_C`.
* `reverse_rootProduct`.
* `card_rootsIn_reverse`.
-/

open Polynomial

namespace CoefficientMass

theorem reverse_prod_fin :
    ∀ (L : ℕ) (p : Fin L → ℝ[X]), (∏ i, p i).reverse = ∏ i, (p i).reverse := by
  intro L
  induction L with
  | zero =>
    intro p
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, ← C_1, reverse_C]
  | succ L ih =>
    intro p
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, reverse_mul_of_domain, ih]

/-- `x - r` reverses to `1 - r t = -r (t - 1/r)`. -/
theorem reverse_X_sub_C {r : ℝ} (hr : r ≠ 0) : (X - C r).reverse = C (-r) * (X - C r⁻¹) := by
  have hX : (X : ℝ[X]).reverse = 1 := by
    rw [← mul_one X, reverse_X_mul, ← C_1, reverse_C]
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, mul_sub,
    ← C_mul, neg_mul, mul_inv_cancel₀ hr, C_neg, C_1]
  ring

theorem reverse_rootProduct {L : ℕ} (r : Fin L → ℝ) (hr : ∀ i, r i ≠ 0) :
    (rootProduct ℝ r).reverse = C (∏ i, -r i) * ∏ i, (X - C (r i)⁻¹) := by
  rw [rootProduct]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [reverse_prod_fin, Finset.prod_congr rfl fun i _ => reverse_X_sub_C (hr i),
    Finset.prod_mul_distrib, map_prod]

/-- `F^*` has at least `L` zeros in `(0, 1/2]`. -/
theorem card_rootsIn_reverse {L : ℕ} (r : Fin L → ℝ) (hr : ∀ i, 2 ≤ r i) (F : ℝ[X])
    (hF : F ≠ 0) (hdvd : rootProduct ℝ r ∣ F) : L ≤ Multiset.card (rootsIn F.reverse) := by
  obtain ⟨Q, rfl⟩ := hdvd
  have hr0 : ∀ i, r i ≠ 0 := fun i => by linarith [hr i]
  set A : Multiset ℝ := (Finset.univ : Finset (Fin L)).val.map fun i => (r i)⁻¹
  have hA : (A.map fun a => X - C a).prod = ∏ i, (X - C (r i)⁻¹) := by
    rw [Multiset.map_map]
    rfl
  have hdvd' : (A.map fun a => X - C a).prod ∣ (rootProduct ℝ r * Q).reverse := by
    rw [hA, reverse_mul_of_domain, reverse_rootProduct r hr0]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hne : (rootProduct ℝ r * Q).reverse ≠ 0 := by
    rwa [Ne, reverse_eq_zero]
  have hle := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne A).1 hdvd'
  have hle' : A ≤ rootsIn (rootProduct ℝ r * Q).reverse := by
    rw [rootsIn]
    refine Multiset.le_filter.2 ⟨hle, fun a ha => ?_⟩
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 ha
    exact ⟨inv_pos.2 (by linarith [hr i]), by rw [one_div]; exact inv_anti₀ two_pos (hr i)⟩
  calc L = Multiset.card A := by
        rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Multiset.card_le_card hle'

end CoefficientMass
