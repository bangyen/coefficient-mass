/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ValsIdent
import CoefficientMass.ValsSplit

/-!
# Counting and Product Bounds for the Kept Holes

This module prepares Lemma 4.10 of `coefficient-mass.tex`.  The `r`-th kept hole `c`
(from `0`) has `r` holes below it and `ℓ - r` above it, all in `[ℓ + 1, m]`, so
`c ≥ ℓ + 1 + r` and `m ≥ c + ℓ - r`; the products of `abs_confPoly_split` are at most
`C(c - 1, |D|)` and `C(c + |D|, |D|)` by their extreme placements.

## Theorems

* `below_card`.
* `above_card`.
* `top_bound`.
* `prod_down_le`.
* `prod_up_le`.
* `mul_bound`.
-/

namespace CoefficientMass

theorem below_card {ℓ c : ℕ} {C : Finset ℕ} (hC : ∀ x ∈ C, ℓ + 1 ≤ x) (hc : ℓ + 1 ≤ c) :
    ℓ + 1 + (C.filter (· < c)).card ≤ c := by
  have h := Finset.card_le_card fun x (hx : x ∈ C.filter (· < c)) =>
    Finset.mem_Ico.2 ⟨hC x (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩
  rw [Nat.card_Ico] at h
  omega

theorem above_card {ℓ c : ℕ} {C : Finset ℕ} (hC : C.card = ℓ + 1) (hc : c ∈ C) :
    (C.filter (c < ·)).card + (C.filter (· < c)).card = ℓ := by
  have h := Finset.card_erase_of_mem hc
  have hdisj : Disjoint (C.filter (· < c)) (C.filter (c < ·)) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => by omega
  rw [erase_eq_filter_union, Finset.card_union_of_disjoint hdisj, hC] at h
  omega

theorem top_bound {c m : ℕ} {C : Finset ℕ} (hC : ∀ x ∈ C, x ≤ m) (hc : c ≤ m) :
    c + (C.filter (c < ·)).card ≤ m := by
  have h := Finset.card_le_card fun x (hx : x ∈ C.filter (c < ·)) =>
    Finset.mem_Ioc.2 ⟨(Finset.mem_filter.1 hx).2, hC x (Finset.mem_filter.1 hx).1⟩
  rw [Nat.card_Ioc] at h
  omega

/-- `∏_{x ∈ D} x / (c - x) ≤ C(c - 1, |D|)` for `D ⊆ [0, c)`. -/
theorem prod_down_le {c : ℕ} (hc : 1 ≤ c) (D : Finset ℕ) (hD : ∀ x ∈ D, x < c) :
    ∏ x ∈ D, ((x : ℝ) / ((c : ℝ) - x)) ≤ pDown D.card c := by
  have hDc := Finset.card_le_card fun x (hx : x ∈ D) => Finset.mem_range.2 (hD x hx)
  rw [Finset.card_range] at hDc
  have key := prod_le_prod_top (g := fun x : ℕ => (x : ℝ) / ((c : ℝ) - x)) (M₀ := c - 1)
    (fun x hx => by
      have : (x : ℝ) + 1 ≤ c := by exact_mod_cast (show x + 1 ≤ c by omega)
      exact div_nonneg (Nat.cast_nonneg x) (by linarith))
    (fun x y hxy hy => by
      have h1 : (y : ℝ) + 1 ≤ c := by exact_mod_cast (show y + 1 ≤ c by omega)
      have h2 : (x : ℝ) ≤ y := by exact_mod_cast hxy
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
    D.card (c - 1) D rfl le_rfl (fun x hx => by have := hD x hx; omega)
  rw [pDown]
  refine key.trans (le_of_eq (Finset.prod_congr rfl fun j hj => ?_))
  have hj := Finset.mem_range.1 hj
  have e : ((c - 1 - j : ℕ) : ℝ) = c - 1 - j := by
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    exact_mod_cast (show c - 1 - j + j + 1 = c by omega)
  change ((c - 1 - j : ℕ) : ℝ) / ((c : ℝ) - ((c - 1 - j : ℕ) : ℝ)) = _
  rw [e, show (c : ℝ) - (c - 1 - j) = j + 1 by ring]

/-- `∏_{x ∈ D} x / (x - c) ≤ C(c + |D|, |D|)` for `D ⊆ (c, ∞)`. -/
theorem prod_up_le (c : ℕ) (D : Finset ℕ) (hD : ∀ x ∈ D, c < x) :
    ∏ x ∈ D, ((x : ℝ) / ((x : ℝ) - c)) ≤ qUp D.card c := by
  have key := prod_le_prod_bot (h := fun x : ℕ => (x : ℝ) / ((x : ℝ) - c)) (lo₀ := c + 1)
    (fun x hx => by
      have : (c : ℝ) + 1 ≤ x := by exact_mod_cast hx
      exact div_nonneg (Nat.cast_nonneg x) (by linarith))
    (fun x y hx hxy => by
      have h1 : (c : ℝ) + 1 ≤ x := by exact_mod_cast hx
      have h2 : (x : ℝ) ≤ y := by exact_mod_cast hxy
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
    D.card (c + 1) D rfl le_rfl (fun x hx => hD x hx)
  rw [qUp]
  refine key.trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
  change ((c + 1 + j : ℕ) : ℝ) / (((c + 1 + j : ℕ) : ℝ) - c) = _
  push_cast
  rw [show (c : ℝ) + 1 + j - c = j + 1 by ring]

theorem mul_bound {p a β β' L L' U U' : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hβ : β ≤ β')
    (hβ0 : 0 ≤ β) (hL : L ≤ L') (hL0 : 0 ≤ L) (hU : U ≤ U') (hU0 : 0 ≤ U) :
    a * β * (L * U) * p ≤ p * (a * β') * L' * U' := by
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hβ ha) (mul_le_mul hL hU hU0 (hL0.trans hL))
    (mul_nonneg hL0 hU0) (mul_nonneg ha (hβ0.trans hβ))
  calc a * β * (L * U) * p ≤ a * β' * (L' * U') * p := mul_le_mul_of_nonneg_right h hp
    _ = p * (a * β') * L' * U' := by ring

end CoefficientMass
