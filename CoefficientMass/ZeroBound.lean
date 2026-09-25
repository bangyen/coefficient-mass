/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ExpSum
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Max

/-!
# The Zero Bound for Exponential Sums

This module proves the zero bound of Section 2 of `coefficient-mass.tex`: a
nonzero exponential sum on `c` distinct positive nodes has at most `c - 1`
real zeros.  Write the sum as `∑ a_i e^{λ_i t}` with distinct `λ_i`, divide
by one exponential, and differentiate: by Rolle's theorem the derivative, a
sum on one fewer node, has at least one zero fewer.  The count here is of
distinct zeros, which is what `ZeroBound` states.

## Theorems

* `card_le_encard_deriv_zero_add_one`.
* `encard_zeros_add_one_le`.
* `zeroBound`.
-/

namespace CoefficientMass

/-- Rolle's theorem, counted: a differentiable function with `n` zeros has a
derivative with at least `n - 1` zeros. -/
theorem card_le_encard_deriv_zero_add_one {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (s : Finset ℝ) (hs : ∀ x ∈ s, g x = 0) :
    (s.card : ℕ∞) ≤ {t | deriv g t = 0}.encard + 1 := by
  rcases Set.finite_or_infinite {t | deriv g t = 0} with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card]
    exact_mod_cast Finset.card_le_of_interleaved fun x hx y hy hxy _ => by
      obtain ⟨z, hz, hz0⟩ :=
        exists_deriv_eq_zero hxy hg.continuous.continuousOn ((hs x hx).trans (hs y hy).symm)
      exact ⟨z, hfin.mem_toFinset.2 hz0, hz.1, hz.2⟩
  · rw [hinf.encard_eq, top_add]
    exact le_top

/-- The zero bound in exponential form: `∑_{i ∈ s} a_i e^{λ_i t}`, with the
`λ_i` distinct and some `a_i ≠ 0`, has at most `|s| - 1` real zeros. -/
theorem encard_zeros_add_one_le {ι : Type*} (s : Finset ι) :
    ∀ a lam : ι → ℝ, Set.InjOn lam s → (∃ i ∈ s, a i ≠ 0) →
      {t : ℝ | ∑ i ∈ s, a i * Real.exp (lam i * t) = 0}.encard + 1 ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a lam _ h
    obtain ⟨i, hi, _⟩ := h
    exact absurd hi (Finset.notMem_empty i)
  | insert j s hj ih =>
    intro a lam hinj h
    rw [Finset.card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one]
    refine add_le_add ?_ le_rfl
    by_cases hs : ∃ i ∈ s, a i ≠ 0
    swap
    · -- only the node `j` is present, and a single exponential has no zero
      push_neg at hs
      have haj : a j ≠ 0 := by
        obtain ⟨i, hi, hai⟩ := h
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hai
        · exact absurd (hs i hi) hai
      have hempty : {t : ℝ | ∑ i ∈ insert j s, a i * Real.exp (lam i * t) = 0} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun t ht => ?_
        rw [Set.mem_setOf_eq, Finset.sum_insert hj,
          Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_mul], add_zero] at ht
        exact mul_ne_zero haj (Real.exp_pos _).ne' ht
      rw [hempty, Set.encard_empty]
      exact zero_le _
    -- divide by `e^{λ_j t}` and differentiate
    set g : ℝ → ℝ := fun t => a j + ∑ i ∈ s, a i * Real.exp ((lam i - lam j) * t) with hg
    set g' : ℝ → ℝ := fun t => ∑ i ∈ s, a i * (lam i - lam j) * Real.exp ((lam i - lam j) * t)
    have hderiv : ∀ t, HasDerivAt g (g' t) t := fun t => by
      refine ((HasDerivAt.fun_sum fun i _ =>
        (((hasDerivAt_id t).const_mul (lam i - lam j)).exp.const_mul (a i))).const_add
          (a j)).congr_deriv ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [id]
      ring
    have hzeros : {t : ℝ | ∑ i ∈ insert j s, a i * Real.exp (lam i * t) = 0} =
        {t | g t = 0} := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Finset.sum_insert hj]
      have he : ∀ i, Real.exp (lam i * t) = Real.exp (lam j * t) * Real.exp ((lam i - lam j) * t) :=
        fun i => by rw [← Real.exp_add]; ring_nf
      simp only [hg]
      rw [he j, sub_self, zero_mul, Real.exp_zero, mul_one,
        Finset.sum_congr rfl fun i _ => by rw [he i, mul_left_comm], ← Finset.mul_sum,
        mul_comm (a j), ← mul_add, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
    have hdz : {t | deriv g t = 0} =
        {t : ℝ | ∑ i ∈ s, a i * (lam i - lam j) * Real.exp ((lam i - lam j) * t) = 0} := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, (hderiv t).deriv]
    have hih := ih (fun i => a i * (lam i - lam j)) (fun i => lam i - lam j)
      (fun x hx y hy hxy => hinj (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
        (sub_left_injective hxy)) (by
        obtain ⟨i, hi, hai⟩ := hs
        refine ⟨i, hi, mul_ne_zero hai (sub_ne_zero.2 fun he => ?_)⟩
        exact hj (hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self j s) he ▸ hi))
    rw [← hdz] at hih
    -- every finite set of zeros has at most `|s|` points
    rw [hzeros]
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨u, hu, hcard⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have hfin : u.Finite := Set.finite_of_encard_eq_coe hcard
    have hr := card_le_encard_deriv_zero_add_one (fun t => (hderiv t).differentiableAt)
      hfin.toFinset fun x hx => hu (hfin.mem_toFinset.1 hx)
    rw [← hfin.encard_eq_coe_toFinset_card, hcard] at hr
    exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.coe_ne_top _)).1 (hr.trans hih))

/-- The zero bound: a nonzero exponential sum on `c` distinct positive nodes
has at most `c - 1` real zeros. -/
theorem zeroBound : ZeroBound := by
  intro c a y hinj hpos ha
  have hrpow : {t : ℝ | ∑ i, a i * y i ^ t = 0} =
      {t : ℝ | ∑ i ∈ Finset.univ, a i * Real.exp (Real.log (y i) * t) = 0} := by
    ext t
    simp only [Set.mem_setOf_eq, Real.rpow_def_of_pos (hpos _)]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have h := encard_zeros_add_one_le Finset.univ a (fun i => Real.log (y i))
    (fun x _ z _ hxz => hinj (Real.log_injOn_pos (hpos x) (hpos z) hxz))
    ⟨i, Finset.mem_univ i, hi⟩
  rw [← hrpow, Finset.card_univ, Fintype.card_fin] at h
  generalize {t : ℝ | ∑ i, a i * y i ^ t = 0}.encard = e at h ⊢
  induction e using ENat.recTopCoe with
  | top => exact absurd h (by rw [top_add, top_le_iff]; exact ENat.coe_ne_top c)
  | coe n =>
    have hn : n + 1 ≤ c := by exact_mod_cast h
    exact_mod_cast (by omega : n ≤ c - 1)

end CoefficientMass
