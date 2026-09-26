/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowValue

/-!
# Row Values as Infima

This module sets up the quantities of Section 2 of `coefficient-mass-rows.tex`.  The `k`-th
largest nonleading magnitude `b_k(F)` is the largest `T` with at least `k` nonleading
magnitudes `≥ T`; the supremum is attained, since below it only finitely many magnitudes
can be crossed.  The row value `V_r(L, k)` is the infimum of `b_k(F)` over monic multiples
`F` of `(x - r)^L`, and `μ_r(S, L)` is the infimum of `Φ_r(q)` over real `q` with
`deg q < L`, `q(0) = 1` and `q|_S = 0`.

## Definitions

* `kthMag`.
* `rowValue`.
* `muR`.

## Theorems

* `largeCount_anti`.
* `largeCount_zero`.
* `bddAbove_kth`.
* `kthMag_mem`.
* `le_largeCount_iff`.
* `kthMag_nonneg`.
-/

open Polynomial

namespace CoefficientMass

/-- `b_k(F)`: the largest `T` with at least `k` nonleading magnitudes `‖f_j‖ ≥ T`. -/
noncomputable def kthMag (F : ℝ[X]) (k : ℕ) : ℝ :=
  sSup {T : ℝ | k ≤ largeCount F T}

/-- `V_r(L, k)`: the infimum of `b_k(F)` over monic real multiples `F` of `(x - r)^L`. -/
noncomputable def rowValue (r : ℝ) (L k : ℕ) : ℝ :=
  ⨅ F : {F : ℝ[X] // F.Monic ∧ (X - C r) ^ L ∣ F}, kthMag F.1 k

/-- `μ_r(S, L)`: the infimum of `Φ_r(q)` over real `q` with `deg q < L`, `q(0) = 1` and
`q|_S = 0`. -/
noncomputable def muR (r : ℝ) (S : Finset ℕ) (L : ℕ) : ℝ :=
  ⨅ q : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0}, rowPhi r q.1

theorem largeCount_anti (F : ℝ[X]) {S T : ℝ} (h : S ≤ T) : largeCount F T ≤ largeCount F S :=
  Finset.card_le_card fun _ hj => by
    obtain ⟨hj, hT⟩ := Finset.mem_filter.1 hj
    exact Finset.mem_filter.2 ⟨hj, h.trans hT⟩

theorem largeCount_zero (F : ℝ[X]) : largeCount F 0 = F.natDegree := by
  rw [largeCount, Finset.filter_true_of_mem fun j _ => norm_nonneg _, Finset.card_range]

theorem bddAbove_kth (F : ℝ[X]) {k : ℕ} (hk : 1 ≤ k) :
    BddAbove {T : ℝ | k ≤ largeCount F T} := by
  refine ⟨∑ j ∈ Finset.range F.natDegree, ‖F.coeff j‖, fun T hT => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h0 : largeCount F T = 0 := by
    rw [largeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hTj
    have := Finset.single_le_sum (f := fun j => ‖F.coeff j‖) (fun _ _ => norm_nonneg _) hj
    linarith
  have : k ≤ largeCount F T := hT
  omega

/-- The supremum defining `b_k(F)` is attained. -/
theorem kthMag_mem {F : ℝ[X]} {k : ℕ} (hkD : k ≤ F.natDegree) :
    k ≤ largeCount F (kthMag F k) := by
  classical
  set A := {T : ℝ | k ≤ largeCount F T}
  have hA : A.Nonempty := ⟨0, show k ≤ largeCount F 0 by rw [largeCount_zero]; exact hkD⟩
  set b := kthMag F k
  set U := (Finset.range F.natDegree).filter fun j => ‖F.coeff j‖ < b
  rcases U.eq_empty_or_nonempty with hU | hU
  · have : largeCount F b = F.natDegree := by
      rw [largeCount, Finset.filter_true_of_mem fun j hj => not_lt.1 fun h =>
        (Finset.eq_empty_iff_forall_notMem.1 hU) j (Finset.mem_filter.2 ⟨hj, h⟩),
        Finset.card_range]
    rw [this]
    exact hkD
  obtain ⟨j₀, hj₀, hmax⟩ := U.exists_max_image (fun j => ‖F.coeff j‖) hU
  obtain ⟨T, hTA, hT⟩ := exists_lt_of_lt_csSup hA (Finset.mem_filter.1 hj₀).2
  have hTA' : k ≤ largeCount F T := hTA
  refine le_trans hTA' (Finset.card_le_card fun j hj => ?_)
  obtain ⟨hjD, hTj⟩ := Finset.mem_filter.1 hj
  refine Finset.mem_filter.2 ⟨hjD, not_lt.1 fun hlt => ?_⟩
  have := hmax j (Finset.mem_filter.2 ⟨hjD, hlt⟩)
  linarith

/-- `b_k(F) ≥ T` exactly when at least `k` nonleading magnitudes are `≥ T`. -/
theorem le_largeCount_iff {F : ℝ[X]} {k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ F.natDegree) {T : ℝ} :
    k ≤ largeCount F T ↔ T ≤ kthMag F k :=
  ⟨fun h => le_csSup (bddAbove_kth F hk) h,
    fun h => (kthMag_mem hkD).trans (largeCount_anti F h)⟩

theorem kthMag_nonneg {F : ℝ[X]} {k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ F.natDegree) :
    0 ≤ kthMag F k :=
  (le_largeCount_iff hk hkD).1 (by rw [largeCount_zero]; exact hkD)

end CoefficientMass
