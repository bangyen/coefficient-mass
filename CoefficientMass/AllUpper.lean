/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Mass
import CoefficientMass.Perturb
import CoefficientMass.TailProd
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The Mass of the Root Product

This module proves the upper bound of Corollary 4.3 of `coefficient-mass.tex`: for
`2 ≤ r_1 ≤ ⋯ ≤ r_L`, `Λ(P) ≤ 3 (L^2 + ∑_i i log (r_i - 1))` for `P = ∏ (x - r_i)`.  By
Vieta, `|p_k|` is a sum of `C(L, k)` products of `L - k` roots, each at most the product
of the `L - k` largest; summing the logarithms over `k` gives
`∑_k log C(L, k) + ∑_i i log r_i`, and `r_i ≤ 2 (r_i - 1)`.

## Theorems

* `sum_Ico_triangle`.
* `abs_coeff_rootProduct_le`.
* `logPlus_le_log`.
* `mass_rootProduct_le`.
-/

open Polynomial

namespace CoefficientMass

/-- `∑_{k ≤ L} ∑_{k ≤ i < L} a_i = ∑_{i < L} (i + 1) a_i`. -/
theorem sum_Ico_triangle (a : ℕ → ℝ) : ∀ L : ℕ,
    ∑ k ∈ Finset.range (L + 1), ∑ i ∈ Finset.Ico k L, a i =
      ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * a i := by
  intro L
  induction L with
  | zero => rw [Finset.sum_range_one, Finset.Ico_self, Finset.sum_empty, Finset.sum_range_zero]
  | succ L ih =>
    rw [Finset.sum_range_succ (n := L + 1), Finset.Ico_self, Finset.sum_empty, add_zero,
      Finset.sum_congr rfl fun k hk =>
        Finset.sum_Ico_succ_top (by have := Finset.mem_range.1 hk; omega) a,
      Finset.sum_add_distrib, ih, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_range_succ (n := L)]
    push_cast
    ring

/-- Vieta: `|p_k| ≤ C(L, k) ∏_{j < L - k} g (L - 1 - j)` for a nondecreasing extension `g`
of the roots. -/
theorem abs_coeff_rootProduct_le {L : ℕ} (hL : 1 ≤ L) (r : Fin L → ℝ) (hmono : Monotone r)
    (hr : ∀ i, 0 ≤ r i) {k : ℕ} (hk : k ≤ L) :
    |(rootProduct ℝ r).coeff k| ≤ (L.choose k : ℝ) *
      ∏ j ∈ Finset.range (L - k), r ⟨min (L - 1 - j) (L - 1), by omega⟩ := by
  set g : ℕ → ℝ := fun n => r ⟨min n (L - 1), by omega⟩ with hg
  have hgr : ∀ i : Fin L, g i = r i := fun i => congrArg r (Fin.ext (Nat.min_eq_left (by omega)))
  have hP : rootProduct ℝ r = ∏ i ∈ (Finset.univ : Finset (Fin L)), (X - C (r i)) := by
    rw [rootProduct]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [hP, Finset.prod_X_sub_C_coeff _ _ (by rw [Finset.card_univ, Fintype.card_fin]; exact hk),
    abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Finset.card_univ, Fintype.card_fin]
  have hbound : ∀ t ∈ Finset.powersetCard (L - k) (Finset.univ : Finset (Fin L)),
      |∏ i ∈ t, r i| ≤ ∏ j ∈ Finset.range (L - k), g (L - 1 - j) := fun t ht => by
    have htc := (Finset.mem_powersetCard.1 ht).2
    rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => hr i)]
    have h := prod_le_prod_top (g := g) (M₀ := L - 1) (fun x _ => hr _)
      (fun x y hxy _ => hmono (Fin.mk_le_mk.2 (min_le_min_right _ hxy)))
      (L - k) (L - 1) (t.map Fin.valEmbedding) (by rw [Finset.card_map, htc]) le_rfl
      fun x hx => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hx
        have := i.isLt
        simp only [Fin.valEmbedding_apply]
        omega
    rw [Finset.prod_map] at h
    simp only [Fin.valEmbedding_apply, hgr] at h
    exact h
  calc |∑ t ∈ Finset.powersetCard (L - k) Finset.univ, ∏ i ∈ t, r i|
      ≤ ∑ t ∈ Finset.powersetCard (L - k) (Finset.univ : Finset (Fin L)), |∏ i ∈ t, r i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.powersetCard (L - k) (Finset.univ : Finset (Fin L)),
          ∏ j ∈ Finset.range (L - k), g (L - 1 - j) := Finset.sum_le_sum hbound
    _ = (L.choose k : ℝ) * ∏ j ∈ Finset.range (L - k), g (L - 1 - j) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          Nat.choose_symm hk, nsmul_eq_mul]

theorem logPlus_le_log {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    logPlus x ≤ Real.log y := by
  refine max_le (Real.log_nonneg hy) ?_
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    exact Real.log_nonneg hy
  · exact Real.log_le_log h hxy

end CoefficientMass
