/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Jensen's Bound for Polynomials

This module proves the case of Jensen's formula that Proposition 4.2 of
`coefficient-mass.tex` uses.  If a real polynomial `g = ∏_{a ∈ A} (x - a) · H` has its
roots `a ∈ A` in `(0, 1/2]` and `|g| ≤ M` on the circle `|t| = R`, then
`|g(0)| (2R)^{|A|} ≤ M`.  Each root `a` is replaced by the factor `R^2 - a x`, which has
modulus `R |t - a|` on the circle and value `R^2 ≥ 2R a` at `0`; the maximum modulus
principle finishes.

## Theorems

* `norm_eval_zero_le`.
* `norm_sq_sub_mul`.
* `jensen_poly`.
-/

open Polynomial

namespace CoefficientMass

/-- The maximum modulus principle for a polynomial on the disc `|t| ≤ R`. -/
theorem norm_eval_zero_le {R M : ℝ} (hR : 0 < R) (H : ℝ[X])
    (hM : ∀ t : ℂ, ‖t‖ = R → ‖(H.map (algebraMap ℝ ℂ)).eval t‖ ≤ M) :
    ‖(H.map (algebraMap ℝ ℂ)).eval 0‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) R)
    Metric.isBounded_ball (Polynomial.differentiable _).diffContOnCl (fun z hz => ?_)
    (subset_closure (Metric.mem_ball_self hR))
  rw [frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm] at hz
  exact hM z hz

/-- On the circle `|t| = R`, `|R^2 - a t| = R |t - a|` for real `a`. -/
theorem norm_sq_sub_mul {R a : ℝ} {t : ℂ} (ht : ‖t‖ = R) :
    ‖((R : ℂ) ^ 2 - a * t)‖ = R * ‖t - a‖ := by
  have hconj : (R : ℂ) ^ 2 = t * (starRingEnd ℂ) t := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ht]
    push_cast
    ring
  rw [hconj, show t * (starRingEnd ℂ) t - a * t = t * ((starRingEnd ℂ) t - a) by ring,
    norm_mul, ht, show (starRingEnd ℂ) t - a = (starRingEnd ℂ) (t - a) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]

/-- Jensen's bound: `|g(0)| (2R)^{|A|} ≤ max_{|t| = R} |g(t)|` for
`g = ∏_{a ∈ A} (x - a) · H` with `A ⊂ (0, 1/2]`. -/
theorem jensen_poly {R : ℝ} (hR : 0 < R) (A : Multiset ℝ) :
    ∀ (H : ℝ[X]) (M : ℝ), (∀ a ∈ A, 0 < a ∧ a ≤ 1 / 2) →
      (∀ t : ℂ, ‖t‖ = R →
        ‖(((A.map fun a => X - C a).prod * H).map (algebraMap ℝ ℂ)).eval t‖ ≤ M) →
      ‖(((A.map fun a => X - C a).prod * H).map (algebraMap ℝ ℂ)).eval 0‖ *
        (2 * R) ^ Multiset.card A ≤ M := by
  induction A using Multiset.induction_on with
  | empty =>
    intro H M _ hM
    rw [Multiset.map_zero, Multiset.prod_zero, one_mul, Multiset.card_zero, pow_zero, mul_one]
    exact norm_eval_zero_le hR H (by simpa only [Multiset.map_zero, Multiset.prod_zero,
      one_mul] using hM)
  | cons a A ih =>
    intro H M hA hM
    have ha := hA a (Multiset.mem_cons_self a A)
    set P := (A.map fun a => X - C a).prod
    have hev : ∀ (p q : ℝ[X]) (t : ℂ), ((p * q).map (algebraMap ℝ ℂ)).eval t =
        (p.map (algebraMap ℝ ℂ)).eval t * (q.map (algebraMap ℝ ℂ)).eval t := fun p q t => by
      rw [Polynomial.map_mul, eval_mul]
    have e1 : ∀ t : ℂ, ((X - C a).map (algebraMap ℝ ℂ)).eval t = t - a := fun t => by
      simp only [Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C,
        Complex.coe_algebraMap]
    have e2 : ∀ t : ℂ, ((C (R ^ 2) - C a * X).map (algebraMap ℝ ℂ)).eval t =
        (R : ℂ) ^ 2 - a * t := fun t => by
      simp only [Polynomial.map_sub, Polynomial.map_mul, map_X, map_C, eval_sub, eval_mul,
        eval_X, eval_C, Complex.coe_algebraMap, Complex.ofReal_pow]
    have hg : ∀ t : ℂ,
        ((((a ::ₘ A).map fun a => X - C a).prod * H).map (algebraMap ℝ ℂ)).eval t =
          (t - a) * ((P * H).map (algebraMap ℝ ℂ)).eval t := fun t => by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_assoc, hev, e1]
    have hg' : ∀ t : ℂ, ((P * ((C (R ^ 2) - C a * X) * H)).map (algebraMap ℝ ℂ)).eval t =
        ((R : ℂ) ^ 2 - a * t) * ((P * H).map (algebraMap ℝ ℂ)).eval t := fun t => by
      rw [hev, hev, hev, e2]
      ring
    have key := ih ((C (R ^ 2) - C a * X) * H) (R * M)
      (fun b hb => hA b (Multiset.mem_cons_of_mem hb)) fun t ht => by
        rw [hg', norm_mul, norm_sq_sub_mul ht, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hR.le
        rw [← norm_mul, ← hg]
        exact hM t ht
    rw [hg', norm_mul] at key
    rw [hg, Multiset.card_cons, pow_succ, norm_mul]
    set u := ‖((P * H).map (algebraMap ℝ ℂ)).eval 0‖
    have hu : 0 ≤ u := norm_nonneg _
    have h0 : ‖((0 : ℂ) - a)‖ = a := by
      rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha.1]
    have h1 : ‖((R : ℂ) ^ 2 - a * 0)‖ = R ^ 2 := by
      rw [mul_zero, sub_zero, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [h0]
    rw [h1] at key
    set X' := (2 * R) ^ Multiset.card A
    have hX : 0 ≤ X' := by positivity
    have k1 : R * (R * u * X') ≤ R * M := by
      calc R * (R * u * X') = R ^ 2 * u * X' := by ring
        _ ≤ R * M := key
    have k2 := le_of_mul_le_mul_left k1 hR
    calc a * u * (X' * (2 * R)) = (a * (2 * R)) * (u * X') := by ring
      _ ≤ R * (u * X') := mul_le_mul_of_nonneg_right (by nlinarith [ha.2, hR])
          (mul_nonneg hu hX)
      _ = R * u * X' := by ring
      _ ≤ M := k2

end CoefficientMass
