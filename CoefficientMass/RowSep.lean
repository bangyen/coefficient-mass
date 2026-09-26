/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A Bounded Solution by Separation

This module proves the duality step of Proposition 2.1(b) of `coefficient-mass-rows.tex`:
the linear system `∑_j a_{ij} g_j = b_i` has a solution with `|g_j| ≤ t` on a set `N` of
positions, the others free, as soon as every `c` with `∑_i c_i a_{ij} = 0` off `N` has
`∑_i c_i b_i ≥ -t ∑_{j ∈ N} |∑_i c_i a_{ij}|`.  The attainable right-hand sides form the sum
of a compact convex set and a subspace, which is closed, so a right-hand side outside it is
separated from it by a linear functional `c`, and testing `c` on the free directions and on
a sign vector violates the hypothesis.

## Theorems

* `exists_bounded_solution`.
-/

namespace CoefficientMass

/-- A solution of `∑_j a_{ij} g_j = b_i` with `|g_j| ≤ t` for `j ∈ N`. -/
theorem exists_bounded_solution {D L : ℕ} (a : Fin L → Fin D → ℝ) (b : Fin L → ℝ)
    (N : Finset (Fin D)) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ c : Fin L → ℝ, (∀ j ∉ N, ∑ i, c i * a i j = 0) →
      -(t * ∑ j ∈ N, |∑ i, c i * a i j|) ≤ ∑ i, c i * b i) :
    ∃ g : Fin D → ℝ, (∀ i, ∑ j, a i j * g j = b i) ∧ ∀ j ∈ N, |g j| ≤ t := by
  classical
  set Ψ : (Fin D → ℝ) →ₗ[ℝ] (Fin L → ℝ) := (Matrix.of a).mulVecLin
  have hΨ : ∀ g i, Ψ g i = ∑ j, a i j * g j := fun _ _ => rfl
  set box : Set (Fin D → ℝ) :=
    Set.pi Set.univ fun j => if j ∈ N then Set.Icc (-t) t else {0}
  let V : Submodule ℝ (Fin D → ℝ) :=
    { carrier := {v | ∀ j ∈ N, v j = 0}
      add_mem' := fun hx hy j hj => by rw [Pi.add_apply, hx j hj, hy j hj, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c x hx j hj => by rw [Pi.smul_apply, hx j hj, smul_zero] }
  set K : Set (Fin L → ℝ) := Ψ '' box + (V.map Ψ : Set (Fin L → ℝ))
  have hconv : Convex ℝ K :=
    ((convex_pi fun j _ => by split_ifs; exacts [convex_Icc _ _, convex_singleton _]).linear_image
      Ψ).add (Submodule.convex _)
  have hclosed : IsClosed K :=
    IsClosed.add_left_of_isCompact (Submodule.closed_of_finiteDimensional _)
      ((isCompact_univ_pi fun j => by
        split_ifs; exacts [isCompact_Icc, isCompact_singleton]).image
        Ψ.continuous_of_finiteDimensional)
  by_contra hne
  push_neg at hne
  have hb : b ∉ K := by
    rintro ⟨_, ⟨c, hc, rfl⟩, _, ⟨v, hv, rfl⟩, hsum⟩
    have hv' : ∀ j ∈ N, v j = 0 := hv
    obtain ⟨j, hj, hlt⟩ := hne (c + v) fun i => by
      change Ψ (c + v) i = b i
      rw [map_add]
      exact congrFun hsum i
    have hcj := hc j (Set.mem_univ j)
    rw [if_pos hj] at hcj
    rw [Pi.add_apply, hv' j hj, add_zero] at hlt
    exact absurd (abs_le.2 hcj) (not_le.2 hlt)
  obtain ⟨f, u, hfb, hK⟩ := geometric_hahn_banach_point_closed hconv hclosed hb
  set c : Fin L → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hf : ∀ y, f y = ∑ i, c i * y i := fun y => by
    have := (f : (Fin L → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ y
    rw [ContinuousLinearMap.coe_coe] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  set A : Fin D → ℝ := fun j => ∑ i, c i * a i j
  have hfΨ : ∀ g, f (Ψ g) = ∑ j, g j * A j := fun g => by
    rw [hf]
    simp only [hΨ, A, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h0box : (0 : Fin D → ℝ) ∈ box := fun j _ => by
    rw [Pi.zero_apply]
    split_ifs
    exacts [⟨by linarith, ht⟩, rfl]
  -- the free directions
  have hfree : ∀ j ∉ N, A j = 0 := by
    intro j hj
    by_contra hA
    set lam := (u - 1) / A j
    have hmem : Ψ (lam • Pi.single j 1) ∈ K := by
      have hV : ∀ k ∈ N, (lam • Pi.single j (1 : ℝ)) k = 0 := fun k hk => by
        rw [Pi.smul_apply, Pi.single_apply, if_neg (fun h => hj (h ▸ hk)), smul_zero]
      refine ⟨Ψ 0, ⟨0, h0box, rfl⟩, Ψ (lam • Pi.single j 1), ⟨_, hV, rfl⟩, ?_⟩
      rw [map_zero, zero_add]
    have := hK _ hmem
    rw [hfΨ, Finset.sum_eq_single j (fun k _ hk => by
      rw [Pi.smul_apply, Pi.single_apply, if_neg hk, smul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h)] at this
    have hlam : lam * A j = u - 1 := div_mul_cancel₀ _ hA
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hlam] at this
    linarith
  -- a sign vector
  set g₀ : Fin D → ℝ := fun j => if j ∈ N then (if 0 ≤ A j then -t else t) else 0
  have hg₀ : g₀ ∈ box := fun j _ => by
    simp only [g₀]
    split_ifs
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
    · rfl
  have hmem : Ψ g₀ ∈ K := ⟨Ψ g₀, ⟨g₀, hg₀, rfl⟩, 0, (V.map Ψ).zero_mem, add_zero _⟩
  have hlow := hK _ hmem
  have hterm : ∀ j, g₀ j * A j = if j ∈ N then -(t * |A j|) else 0 := fun j => by
    simp only [g₀]
    split_ifs with hj hA
    · rw [abs_of_nonneg hA]; ring
    · rw [abs_of_neg (not_le.1 hA)]; ring
    · rw [zero_mul]
  have hval : f (Ψ g₀) = -(t * ∑ j ∈ N, |A j|) := by
    rw [hfΨ, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hval] at hlow
  have hcb := h c hfree
  rw [hf] at hfb
  linarith

end CoefficientMass
