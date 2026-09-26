/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowSep
import CoefficientMass.RowTaylor

/-!
# Small Multiples from the Truncated Dual

This module proves the truncated duality in the proof of Proposition 2.1(b) of
`coefficient-mass-rows.tex`.  If every real `q` with `deg q < L`, `q(0) = 1` and `q|_S = 0`
has `∑_{s = 1}^D |q(s)| r^{-s} ≥ m > 0`, then some monic multiple
`F = x^D + ∑_{j < D} g_j x^j` of `(x - r)^L` has `|g_j| ≤ 1/m` whenever `D - j ∉ S`.  The
dual vector `c` of the separation step is the polynomial `p = ∑_i c_i binom(s, i)`, and
`q(s) = p(D - s)/p(D)` is admissible.

## Theorems

* `natDegree_binomSum_le`.
* `binomSum_eval`.
* `exists_rowPoly_small`.
-/

open Polynomial

namespace CoefficientMass

theorem natDegree_binomSum_le {L : ℕ} (c : Fin L → ℝ) :
    (∑ i : Fin L, C (c i) * binomPoly i).natDegree ≤ L - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans ((binomPoly_natDegree i).trans (by omega))

theorem binomSum_eval {L : ℕ} (c : Fin L → ℝ) (n : ℕ) :
    (∑ i : Fin L, C (c i) * binomPoly i).eval (n : ℝ) = ∑ i : Fin L, c i * n.choose i := by
  rw [eval_finset_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C, binomPoly_eval]

/-- A monic multiple of `(x - r)^L` of degree `D` with `|f_j| ≤ 1/m` whenever `D - j ∉ S`. -/
theorem exists_rowPoly_small {r : ℝ} (hr : 1 < r) {L D : ℕ} {S : Finset ℕ}
    (hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ D) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 → (∀ s ∈ S, q.eval (s : ℝ) = 0) →
      m ≤ ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) :
    ∃ F : ℝ[X], F.Monic ∧ F.natDegree = D ∧ (X - C r) ^ L ∣ F ∧
      ∀ j < D, D - j ∉ S → ‖F.coeff j‖ ≤ 1 / m := by
  classical
  have hr0 : r ≠ 0 := by positivity
  set a : Fin L → Fin D → ℝ := fun i j => ((j : ℕ).choose i : ℝ) * r ^ (j : ℕ)
  set b : Fin L → ℝ := fun i => -((D.choose i : ℝ) * r ^ D)
  set N := Finset.univ.filter fun j : Fin D => D - (j : ℕ) ∉ S
  have hyp : ∀ c : Fin L → ℝ, (∀ j ∉ N, ∑ i, c i * a i j = 0) →
      -(1 / m * ∑ j ∈ N, |∑ i, c i * a i j|) ≤ ∑ i, c i * b i := by
    intro c hc
    set p := ∑ i : Fin L, C (c i) * binomPoly i
    have hpe : ∀ n : ℕ, p.eval (n : ℝ) = ∑ i : Fin L, c i * n.choose i := binomSum_eval c
    have hA : ∀ j : Fin D, ∑ i, c i * a i j = r ^ (j : ℕ) * p.eval ((j : ℕ) : ℝ) := fun j => by
      rw [hpe, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [a]; ring
    have hcb : ∑ i, c i * b i = -(r ^ D * p.eval (D : ℝ)) := by
      rw [hpe, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [b]; ring
    rw [hcb, neg_le_neg_iff]
    have hsum0 : 0 ≤ ∑ j ∈ N, |∑ i, c i * a i j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases le_or_gt (p.eval (D : ℝ)) 0 with hp | hp
    · have : r ^ D * p.eval (D : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hp
      have : 0 ≤ 1 / m * ∑ j ∈ N, |∑ i, c i * a i j| := mul_nonneg (by positivity) hsum0
      linarith
    -- the admissible `q(s) = p(D - s) / p(D)`
    set q := C (1 / p.eval (D : ℝ)) * p.comp (C (D : ℝ) - X)
    have hq : ∀ y : ℝ, q.eval y = p.eval ((D : ℝ) - y) / p.eval (D : ℝ) := fun y => by
      rw [eval_mul, eval_C, eval_comp, eval_sub, eval_C, eval_X]
      ring
    have hqdeg : q.degree < L := by
      have hL : 0 < L := by
        rcases Nat.eq_zero_or_pos L with h | h
        · subst h
          rw [hpe, Fin.sum_univ_zero] at hp
          exact absurd hp (lt_irrefl 0)
        · exact h
      have h1 : (C (D : ℝ) - X).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le ((natDegree_C _).trans_le zero_le_one) natDegree_X_le)
      have h2 : q.natDegree ≤ L - 1 :=
        (natDegree_C_mul_le _ _).trans ((natDegree_comp_le (p := p)).trans
          ((Nat.mul_le_mul (natDegree_binomSum_le c) h1).trans (by omega)))
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show q.natDegree < L by omega))
    have hq0 : q.eval 0 = 1 := by rw [hq, sub_zero, div_self hp.ne']
    have hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0 := fun s hs => by
      obtain ⟨hs1, hsD⟩ := hS s hs
      have hj : D - s < D := by omega
      have hjN : (⟨D - s, hj⟩ : Fin D) ∉ N := fun h =>
        (Finset.mem_filter.1 h).2 (show D - (D - s) ∈ S by rwa [show D - (D - s) = s by omega])
      have h0 : r ^ (D - s) * p.eval ((D - s : ℕ) : ℝ) = 0 := (hA ⟨D - s, hj⟩).symm.trans (hc _ hjN)
      rw [hq, ← Nat.cast_sub hsD, (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hr0), zero_div]
    have hmq := hmin q hqdeg hq0 hqS
    -- the truncated sum of `q` is the weighted sum of `p`
    have hN : ∑ j ∈ N, |∑ i, c i * a i j| = ∑ j ∈ Finset.range D, |r ^ j * p.eval (j : ℝ)| := by
      rw [Finset.sum_subset (Finset.subset_univ N) fun j _ hj => by rw [hc j hj, abs_zero],
        ← Fin.sum_univ_eq_sum_range (fun j => |r ^ j * p.eval (j : ℝ)|) D]
      exact Finset.sum_congr rfl fun j _ => by rw [hA]
    have hleft : ∑ j ∈ Finset.range D, |q.eval ((D : ℝ) - j)| * r ^ j =
        (∑ j ∈ Finset.range D, |r ^ j * p.eval (j : ℝ)|) / p.eval (D : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hq, sub_sub_cancel, abs_div, abs_of_pos hp, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < r ^ j)]
      ring
    have hrefl := sum_reflect hr0 q D
    rw [hleft, ← hN] at hrefl
    have hpos : 0 < r ^ D * p.eval (D : ℝ) := by positivity
    rw [one_div_mul_eq_div, le_div_iff₀ hm]
    calc r ^ D * p.eval (D : ℝ) * m
        ≤ r ^ D * p.eval (D : ℝ) *
            ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left hmq hpos.le
      _ = ∑ j ∈ N, |∑ i, c i * a i j| := by
          rw [mul_comm (r ^ D), mul_assoc, ← hrefl, mul_comm (p.eval (D : ℝ)),
            div_mul_cancel₀ _ hp.ne']
  obtain ⟨g, hg, hgN⟩ := exists_bounded_solution a b N (t := 1 / m) (by positivity) hyp
  refine ⟨rowPoly D g, rowPoly_monic D g, rowPoly_natDegree D g,
    dvd_of_hasseDeriv fun i hi => ?_, fun j hj hjS => ?_⟩
  · have h := hasseDeriv_rowPoly r D g i
    have h2 : ∑ j : Fin D, ((j : ℕ).choose i : ℝ) * r ^ (j : ℕ) * g j =
        -((D.choose i : ℝ) * r ^ D) := hg ⟨i, hi⟩
    rw [h2, add_neg_cancel] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hr0)
  · rw [show (rowPoly D g).coeff j = g ⟨j, hj⟩ from rowPoly_coeff D g ⟨j, hj⟩,
      Real.norm_eq_abs]
    exact hgN _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hjS⟩)

end CoefficientMass
