/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleBeta

/-!
# The Product Beyond the Kept Holes

This module proves the first step of Lemma 4.11 of `coefficient-mass.tex`.  Let
`C ⊂ ℕ_{>0}` have `ℓ + 1` elements, all at most `m`, with `ℓ + 1 ∈ C` and
`m ≥ 2ℓ + 1`.  For `s > m`, `c / (s - c)` increases with `c`, so the `ℓ` elements of
`C \ {ℓ + 1}` contribute at most the values at `m, m - 1, …, m - ℓ + 1`, and
`(ℓ + 1) / (s - ℓ - 1) ≤ (ℓ + 1) / (s - m + ℓ)`:
`∏_{c ∈ C} c / (s - c) ≤ (ℓ + 1) ∏_{j < ℓ} (m - j) / ∏_{j ≤ ℓ} (s - m + j)`.
The right side is `(ℓ + 1) (∏_{j < ℓ} (m - j) / ℓ!) ∫_0^1 t^ℓ (1 - t)^{s - m - 1} dt`.

## Theorems

* `prod_le_prod_top`.
* `prod_hole_div_le`.
* `betaI_mul_prod`.
* `prod_sub_mul_factorial`.
-/

namespace CoefficientMass

/-- For `g` nonnegative and nondecreasing on `[0, M₀]`, the product of `g` over `k` distinct
points of `[0, M]` is at most its product over `M, M - 1, …, M - k + 1`. -/
theorem prod_le_prod_top {g : ℕ → ℝ} {M₀ : ℕ} (hg0 : ∀ x ≤ M₀, 0 ≤ g x)
    (hg : ∀ x y, x ≤ y → y ≤ M₀ → g x ≤ g y) : ∀ (k M : ℕ) (D : Finset ℕ), D.card = k →
      M ≤ M₀ → (∀ x ∈ D, x ≤ M) → ∏ x ∈ D, g x ≤ ∏ j ∈ Finset.range k, g (M - j) := by
  intro k
  induction k with
  | zero =>
    intro M D hD _ _
    rw [Finset.card_eq_zero.1 hD, Finset.prod_empty, Finset.range_zero, Finset.prod_empty]
  | succ k ih =>
    intro M D hD hM hDM
    have hne : D.Nonempty := Finset.card_pos.1 (by omega)
    set d := D.max' hne
    have hdD : d ∈ D := D.max'_mem hne
    have hd : d ≤ M := hDM d hdD
    have hD' : ∀ x ∈ D.erase d, x ≤ M - 1 := fun x hx => by
      have := lt_of_le_of_ne (D.le_max' x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
      omega
    have h1 := ih (M - 1) (D.erase d)
      (by rw [Finset.card_erase_of_mem hdD, hD, Nat.add_sub_cancel]) (by omega) hD'
    rw [← Finset.mul_prod_erase D g hdD, Finset.prod_range_succ', Nat.sub_zero, mul_comm (g d)]
    exact mul_le_mul (h1.trans (le_of_eq (Finset.prod_congr rfl fun j _ => by
      rw [show M - 1 - j = M - (j + 1) by omega]))) (hg d M hd hM) (hg0 d (hd.trans hM))
      (Finset.prod_nonneg fun j _ => hg0 _ (by omega))

/-- `∏_{c ∈ C} c / (s - c) ≤ (ℓ + 1) ∏_{j < ℓ} (m - j) / ∏_{j ≤ ℓ} (s - m + j)`. -/
theorem prod_hole_div_le {ℓ m s : ℕ} {C : Finset ℕ} (hC : C.card = ℓ + 1) (h1 : ℓ + 1 ∈ C)
    (hle : ∀ c ∈ C, c ≤ m) (hm : 2 * ℓ + 1 ≤ m) (hs : m < s) :
    ∏ c ∈ C, ((c : ℝ) / ((s : ℝ) - c)) ≤ (ℓ + 1) * ((∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) /
      ∏ j ∈ Finset.range (ℓ + 1), ((s : ℝ) - m + j)) := by
  have hg0 : ∀ x ≤ s - 1, 0 ≤ (x : ℝ) / ((s : ℝ) - x) := fun x hx => by
    have : (x : ℝ) < s := by exact_mod_cast (show x < s by omega)
    exact div_nonneg (Nat.cast_nonneg x) (by linarith)
  have hmono : ∀ x y, x ≤ y → y ≤ s - 1 → (x : ℝ) / ((s : ℝ) - x) ≤ (y : ℝ) / ((s : ℝ) - y) :=
    fun x y hxy hy => by
    have h1 : (x : ℝ) ≤ y := by exact_mod_cast hxy
    have h2 : (y : ℝ) < s := by exact_mod_cast (show y < s by omega)
    exact div_le_div₀ (Nat.cast_nonneg y) h1 (by linarith) (by linarith)
  have htop := prod_le_prod_top (g := fun x : ℕ => (x : ℝ) / ((s : ℝ) - x)) hg0 hmono ℓ m
    (C.erase (ℓ + 1)) (by rw [Finset.card_erase_of_mem h1, hC, Nat.add_sub_cancel]) (by omega)
    fun x hx => hle x (Finset.mem_of_mem_erase hx)
  have hs' : (m : ℝ) < s := by exact_mod_cast hs
  have hml : (2 * ℓ + 1 : ℝ) ≤ m := by exact_mod_cast hm
  have htop' : ∏ j ∈ Finset.range ℓ, (((m - j : ℕ) : ℝ) / ((s : ℝ) - ((m - j : ℕ) : ℝ))) =
      (∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) / ∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    rw [Nat.cast_sub (by omega)]
    ring
  have hP : 0 ≤ ∏ j ∈ Finset.range ℓ, ((m : ℝ) - j) := Finset.prod_nonneg fun j hj => by
    have : (j : ℝ) ≤ m := by exact_mod_cast (show j ≤ m by have := Finset.mem_range.1 hj; omega)
    linarith
  have hQ : 0 < ∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j) :=
    Finset.prod_pos fun j _ => by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hl1 : ((ℓ + 1 : ℕ) : ℝ) = ℓ + 1 := by push_cast; ring
  rw [← Finset.mul_prod_erase C _ h1, hl1, Finset.prod_range_succ]
  calc (ℓ + 1) / ((s : ℝ) - (ℓ + 1)) * ∏ x ∈ C.erase (ℓ + 1), ((x : ℝ) / ((s : ℝ) - x))
      ≤ (ℓ + 1) / ((s : ℝ) - (ℓ + 1)) * ((∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) /
          ∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j)) :=
        mul_le_mul_of_nonneg_left (htop.trans (le_of_eq htop')) (div_nonneg (by positivity)
          (by linarith))
    _ = (ℓ + 1) * (∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) /
          ((s - (ℓ + 1)) * ∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j)) := by
        rw [div_mul_div_comm]
    _ ≤ (ℓ + 1) * (∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) /
          ((∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j)) * ((s : ℝ) - m + ℓ)) := by
        refine div_le_div_of_nonneg_left (mul_nonneg (by positivity) hP)
          (mul_pos hQ (by linarith)) ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (by linarith) hQ.le
    _ = (ℓ + 1) * ((∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) /
          ((∏ j ∈ Finset.range ℓ, ((s : ℝ) - m + j)) * ((s : ℝ) - m + ℓ))) := by
        rw [mul_div_assoc]

/-- `∫_0^1 t^ℓ (1 - t)^n dt · ∏_{j ≤ ℓ} (n + 1 + j) = ℓ!`. -/
theorem betaI_mul_prod (ℓ n : ℕ) :
    betaI ℓ n * ∏ j ∈ Finset.range (ℓ + 1), ((n : ℝ) + 1 + j) = ℓ.factorial := by
  have h : ∀ ℓ : ℕ, (n.factorial : ℝ) * ∏ j ∈ Finset.range (ℓ + 1), ((n : ℝ) + 1 + j) =
      (ℓ + n + 1).factorial := by
    intro ℓ
    induction ℓ with
    | zero =>
      rw [Finset.prod_range_one, Nat.zero_add, Nat.factorial_succ]
      push_cast
      ring
    | succ ℓ ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, show ℓ + 1 + n + 1 = ℓ + n + 1 + 1 by ring,
        Nat.factorial_succ (ℓ + n + 1)]
      push_cast
      ring
  have hf : ((ℓ + n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [betaI_eq, div_mul_eq_mul_div, mul_assoc, h, div_eq_iff hf]

/-- `∏_{j < ℓ} (m - j) · (m - ℓ)! = m!` for `ℓ ≤ m`. -/
theorem prod_sub_mul_factorial {m : ℕ} : ∀ ℓ, ℓ ≤ m →
    (∏ j ∈ Finset.range ℓ, ((m : ℝ) - j)) * ((m - ℓ).factorial : ℝ) = m.factorial := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    rw [Finset.prod_range_zero, one_mul, Nat.sub_zero]
  | succ ℓ ih =>
    intro h
    have e : m - ℓ = m - (ℓ + 1) + 1 := by omega
    rw [Finset.prod_range_succ, ← ih (by omega), e, Nat.factorial_succ, Nat.cast_mul,
      show ((m - (ℓ + 1) + 1 : ℕ) : ℝ) = (m : ℝ) - ℓ by push_cast [Nat.cast_sub h]; ring]
    ring

end CoefficientMass
