/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleInt
import CoefficientMass.TailProd

/-!
# The Value at One Kept Hole

This module prepares Lemma 4.10 of `coefficient-mass.tex`.  At a kept hole `c` with
the holes `L` below and `U` above it, `|ψ(c)| = c B(N - c + 1, c) ∏_{c' ∈ L} c' / (c - c')
∏_{c' ∈ U} c' / (c' - c)`.  The factor `c' / (c - c')` increases and `c' / (c' - c)`
decreases in `c'`, so the products are largest when `L \ {ℓ + 1}` sits just below `c` and
`U` just above it; `B(N - c + 1, c)` decreases in `N`.

## Theorems

* `prod_le_prod_bot`.
* `erase_eq_filter_union`.
* `abs_confPoly_split`.
* `betaI_anti`.
-/

namespace CoefficientMass

/-- For `h` nonnegative and nonincreasing on `[lo, ∞)`, the product of `h` over `k` distinct
points of `[lo, ∞)` is at most its product over `lo, lo + 1, …, lo + k - 1`. -/
theorem prod_le_prod_bot {h : ℕ → ℝ} {lo₀ : ℕ} (hh0 : ∀ x, lo₀ ≤ x → 0 ≤ h x)
    (hh : ∀ x y, lo₀ ≤ x → x ≤ y → h y ≤ h x) : ∀ (k lo : ℕ) (D : Finset ℕ), D.card = k →
      lo₀ ≤ lo → (∀ x ∈ D, lo ≤ x) → ∏ x ∈ D, h x ≤ ∏ j ∈ Finset.range k, h (lo + j) := by
  intro k
  induction k with
  | zero =>
    intro lo D hD _ _
    rw [Finset.card_eq_zero.1 hD, Finset.prod_empty, Finset.range_zero, Finset.prod_empty]
  | succ k ih =>
    intro lo D hD hlo hDlo
    have hne : D.Nonempty := Finset.card_pos.1 (by omega)
    set d := D.min' hne
    have hdD : d ∈ D := D.min'_mem hne
    have hd : lo ≤ d := hDlo d hdD
    have hD' : ∀ x ∈ D.erase d, lo + 1 ≤ x := fun x hx => by
      have := lt_of_le_of_ne (D.min'_le x (Finset.mem_of_mem_erase hx))
        (Finset.ne_of_mem_erase hx).symm
      omega
    have h1 := ih (lo + 1) (D.erase d)
      (by rw [Finset.card_erase_of_mem hdD, hD, Nat.add_sub_cancel]) (by omega) hD'
    rw [← Finset.mul_prod_erase D h hdD, Finset.prod_range_succ', Nat.add_zero, mul_comm (h d)]
    exact mul_le_mul (h1.trans (le_of_eq (Finset.prod_congr rfl fun j _ => by
      rw [show lo + 1 + j = lo + (j + 1) by omega]))) (hh lo d hlo hd) (hh0 d (hlo.trans hd))
      (Finset.prod_nonneg fun j _ => hh0 _ (by omega))

theorem erase_eq_filter_union (C : Finset ℕ) (c : ℕ) :
    C.erase c = C.filter (· < c) ∪ C.filter (c < ·) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
  omega

/-- `|ψ(c)| = c B(N - c + 1, c) ∏_{c' ∈ L} c' / (c - c') ∏_{c' ∈ U} c' / (c' - c)`. -/
theorem abs_confPoly_split {N : ℕ} {C : Finset ℕ} (h0 : 0 ∉ C) (hle : ∀ c ∈ C, c ≤ N) {c : ℕ}
    (hc : c ∈ C) : |confPoly (Finset.Icc 1 N \ C) c| = (c : ℝ) * betaI (N - c) (c - 1) *
      ((∏ x ∈ C.filter (· < c), ((x : ℝ) / ((c : ℝ) - x))) *
        ∏ x ∈ C.filter (c < ·), ((x : ℝ) / ((x : ℝ) - c))) := by
  rw [abs_confPoly_hole h0 hle hc, holeWeight, abs_div, Finset.abs_prod, Finset.abs_prod]
  simp only [Nat.abs_cast]
  have hdisj : Disjoint (C.filter (· < c)) (C.filter (c < ·)) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => by omega
  have hL : ∏ x ∈ C.filter (· < c), |(c : ℝ) - x| = ∏ x ∈ C.filter (· < c), ((c : ℝ) - x) :=
    Finset.prod_congr rfl fun x hx => abs_of_pos (sub_pos.2 (by
      exact_mod_cast (Finset.mem_filter.1 hx).2))
  have hU : ∏ x ∈ C.filter (c < ·), |(c : ℝ) - x| = ∏ x ∈ C.filter (c < ·), ((x : ℝ) - c) :=
    Finset.prod_congr rfl fun x hx => by
      rw [abs_sub_comm]
      exact abs_of_pos (sub_pos.2 (by exact_mod_cast (Finset.mem_filter.1 hx).2))
  rw [← Finset.mul_prod_erase C _ hc, erase_eq_filter_union, Finset.prod_union hdisj,
    Finset.prod_union hdisj, hL, hU, Finset.prod_div_distrib, Finset.prod_div_distrib]
  ring

/-- `B(a + 1, b + 1)` decreases in `a`. -/
theorem betaI_anti {a a' : ℕ} (h : a ≤ a') (b : ℕ) : betaI a' b ≤ betaI a b := by
  refine intervalIntegral.integral_mono_on zero_le_one
    ((by fun_prop : Continuous fun v : ℝ => v ^ a' * (1 - v) ^ b).intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun v : ℝ => v ^ a * (1 - v) ^ b).intervalIntegrable 0 1)
    fun v hv => mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hv.1 hv.2 h)
      (pow_nonneg (by linarith [hv.2]) b)

end CoefficientMass
