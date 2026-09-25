/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Order

/-!
# From Order Statistics to Mass

This module proves the last step of the chain: Corollary 3.4 of
`coefficient-mass.tex` from Corollary 3.3.  The paper sums `log⁺` over the
positions of the `L` largest nonleading coefficients and the leading one.
Here the order statistics are counts, so the positions are chosen by
induction instead of by sorting: `sum_log_le_sum_logPlus` peels off one
position above the first threshold and passes the remaining thresholds on.

## Theorems

* `sum_log_le_sum_logPlus`.
* `mass_eq_sum_range`.
* `sum_log_threshold`.
* `logarithmicMass_of_complexOrderStatistics`.
-/

open Polynomial

namespace CoefficientMass

/-- Counted thresholds bound `log⁺` mass: if at least `u + 1` of the values
`v j`, `j ∈ s`, reach the positive threshold `t u` for every `u`, then
`∑ log (t u) ≤ ∑_{j ∈ s} log⁺ (v j)`.  No ordering of the thresholds is
needed. -/
theorem sum_log_le_sum_logPlus {n : ℕ} (s : Finset ℕ) (v : ℕ → ℝ) (t : Fin n → ℝ)
    (ht : ∀ u, 0 < t u)
    (hcount : ∀ u : Fin n, u.val + 1 ≤ (s.filter fun j => t u ≤ v j).card) :
    ∑ u, Real.log (t u) ≤ ∑ j ∈ s, logPlus (v j) := by
  induction n generalizing s with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact Finset.sum_nonneg fun j _ => logPlus_nonneg (v j)
  | succ n ih =>
    obtain ⟨j, hj⟩ : (s.filter fun j => t 0 ≤ v j).Nonempty := by
      rw [← Finset.card_pos]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hcount 0)
    rw [Finset.mem_filter] at hj
    rw [Fin.sum_univ_succ, ← Finset.add_sum_erase s _ hj.1]
    refine add_le_add ?_ (ih (s.erase j) (fun u => t u.succ) (fun u => ht u.succ) ?_)
    · exact (Real.log_le_log (ht 0) hj.2).trans (le_max_right 0 _)
    · intro u
      have h := hcount u.succ
      rw [Fin.val_succ] at h
      rw [Finset.filter_erase]
      have := Finset.pred_card_le_card_erase (s := s.filter fun j' => t u.succ ≤ v j') (a := j)
      omega

/-- The mass is the sum of `log⁺ |f_j|` over every position up to the degree;
positions outside the support contribute `log⁺ 0 = 0`. -/
theorem mass_eq_sum_range (F : ℂ[X]) :
    mass F = ∑ j ∈ Finset.range (F.natDegree + 1), logPlus ‖F.coeff j‖ := by
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
  · exact Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_mem_supp j hj))
  · rw [Polynomial.notMem_support_iff.1 hj, norm_zero, logPlus, Real.log_zero, max_self]

/-- The thresholds of Theorem 3.2 sum to the weights of Corollary 3.4:
`∑_u log (c ∏_{i ≥ u} (r_i - 1)) = L log c + ∑_i (i + 1) log (r_i - 1)`. -/
theorem sum_log_threshold {L : ℕ} (r : Fin L → ℝ) (hr : ∀ i, 2 ≤ r i) {c : ℝ}
    (hc : 0 < c) :
    ∑ u : Fin L, Real.log (c * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1)) =
      L * Real.log c + ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) := by
  have hpos : ∀ i, r i - 1 ≠ 0 := fun i => by linarith [hr i]
  have hsplit : ∀ u : Fin L, Real.log (c * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1)) =
      Real.log c + ∑ i ∈ Finset.univ.filter (u ≤ ·), Real.log (r i - 1) := fun u => by
    rw [Real.log_mul hc.ne' (Finset.prod_ne_zero_iff.2 fun i _ => hpos i),
      Real.log_prod fun i _ => hpos i]
  rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (· ≤ i))
    (fun u i => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Finset.filter_le_eq_Iic, Fin.card_Iic]
  push_cast
  ring

/-- Corollary 3.4 from Corollary 3.3: the `L` rows give `L` positions below the
degree whose `log⁺` add up to the row thresholds, and the leading coefficient
contributes `log |f_D|` once more. -/
theorem logarithmicMass_of_complexOrderStatistics (h : ComplexOrderStatistics) :
    LogarithmicMass := by
  intro L r F hmono hr hF hdvd
  have hc : 0 < ‖F.leadingCoeff‖ := norm_pos_iff.2 (leadingCoeff_ne_zero.2 hF)
  have hrow := h L r F hmono hr hF hdvd
  have hsum := sum_log_le_sum_logPlus (Finset.range F.natDegree) (fun j => ‖F.coeff j‖)
    (fun u : Fin L => ‖F.leadingCoeff‖ * ∏ i ∈ Finset.univ.filter (u ≤ ·), (r i - 1))
    (fun u => mul_pos hc (Finset.prod_pos fun i _ => by linarith [hr i])) hrow
  rw [sum_log_threshold r hr hc] at hsum
  rw [mass_eq_sum_range, Finset.sum_range_succ]
  have hlead : Real.log ‖F.leadingCoeff‖ ≤ logPlus ‖F.coeff F.natDegree‖ :=
    le_max_right 0 _
  push_cast
  linarith

end CoefficientMass
