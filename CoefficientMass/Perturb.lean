/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Perturbing the Roots

Theorem 3.2 of `coefficient-mass.tex` reaches repeated roots by moving them
apart, `r_i ↦ r_i + i ε`, and letting `ε → 0`.  This module supplies what that
limit needs: the root product is monic of degree `L`, and the coefficients of
`rootProduct ℝ (r + i ε) * Q` depend continuously on `ε`.

## Theorems

* `rootProduct_monic`.
* `natDegree_rootProduct`.
* `continuous_coeff_mul`.
* `continuous_coeff_prod`.
* `continuous_coeff_rootProduct_mul`.
-/

open Polynomial

namespace CoefficientMass

theorem rootProduct_monic {L : ℕ} (r : Fin L → ℝ) : (rootProduct ℝ r).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_rootProduct {L : ℕ} (r : Fin L → ℝ) : (rootProduct ℝ r).natDegree = L := by
  rw [rootProduct, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem continuous_coeff_mul {p q : ℝ → ℝ[X]} (hp : ∀ n, Continuous fun ε => (p ε).coeff n)
    (hq : ∀ n, Continuous fun ε => (q ε).coeff n) (n : ℕ) :
    Continuous fun ε => (p ε * q ε).coeff n := by
  simp only [coeff_mul]
  exact continuous_finset_sum _ fun x _ => (hp x.1).mul (hq x.2)

theorem continuous_coeff_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ[X])
    (hf : ∀ i ∈ s, ∀ n, Continuous fun ε => (f i ε).coeff n) :
    ∀ n, Continuous fun ε => (∏ i ∈ s, f i ε).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty]
    exact continuous_const
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact continuous_coeff_mul (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The coefficients of `∏ (x - r_i - i ε) * Q` are continuous in `ε`. -/
theorem continuous_coeff_rootProduct_mul {L : ℕ} (r : Fin L → ℝ) (Q : ℝ[X]) (n : ℕ) :
    Continuous fun ε : ℝ =>
      (rootProduct ℝ (fun i => r i + (i.val : ℝ) * ε) * Q).coeff n := by
  refine continuous_coeff_mul (p := fun ε => rootProduct ℝ (fun i => r i + (i.val : ℝ) * ε))
    (continuous_coeff_prod _ _ fun i _ m => ?_) (fun _ => continuous_const) n
  simp only [coeff_sub, coeff_C, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hm : m = 0
  · simp only [if_pos hm]
    exact continuous_const.sub (continuous_const.add (continuous_const.mul continuous_id))
  · simp only [if_neg hm]
    exact continuous_const

end CoefficientMass
