/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleFill
import CoefficientMass.HoleOne
import CoefficientMass.HoleTwo

/-!
# Rows Away from the Top Three Positions

This module proves the first part of Proposition 4.9 of `coefficient-mass.tex`:
`(∗_n)` for every `A` with `{1, 2, 3} ⊄ A`.  With `c_1 < c_2 < ⋯` the holes of `A`,
`c_1 ≤ 3`.  For `c_1 = 1` and `c_1 = 2` keep the hole `c_1`; the one-hole values give
`Φ(Y) = 1 / N ≤ 1 / n` and `Φ(Y) = 1 / (N - 1) ≤ 1 / n`.  For `c_1 = 3` keep `{3, c_2}`;
deleting down to `N = c_2 + n - 1` and Lemma 4.8 give `Φ(Y) ≤ 1 / n`.

## Definitions

* `RowsFree`.

## Theorems

* `mem_of_lt_hole`.
* `star_one`.
* `one_div_le_one_div_nat`.
* `rowsFree`.
-/

namespace CoefficientMass

/-- Proposition 4.9 (rows away from the top three positions): for `n ≥ 1` and finite
`A ⊂ ℕ_{>0}` with `{1, 2, 3} ⊄ A`, some finite `Z ⊇ A` has `|Z| ≤ |A| + n - 1` and
`Φ(Z) ≤ 1 / n`. -/
def RowsFree : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A : Finset ℕ, 0 ∉ A → ¬({1, 2, 3} ⊆ A) →
    ∃ Z : Finset ℕ, A ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 ≤ A.card + n ∧ confTail Z ≤ 1 / n

/-- The positive integers below the first hole lie in `A`. -/
theorem mem_of_lt_hole {A : Finset ℕ} {x : ℕ} (hx : 0 < x) (hlt : x < hole A 0) : x ∈ A := by
  by_contra hxA
  obtain ⟨i, hi, hix⟩ := exists_hole_eq hx hxA hlt.le
  obtain rfl : i = 0 := by omega
  omega

/-- `(∗_1)`: `Z = A`, by Lemma 4.6. -/
theorem star_one {A : Finset ℕ} (h0 : 0 ∉ A) :
    ∃ Z : Finset ℕ, A ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 ≤ A.card + 1 ∧ confTail Z ≤ 1 / ((1 : ℕ) : ℝ) :=
  ⟨A, subset_rfl, h0, le_rfl, by rw [Nat.cast_one, div_one]; exact confTail_le_one _ A rfl h0⟩

theorem one_div_le_one_div_nat {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    1 / (b : ℝ) ≤ 1 / (a : ℝ) :=
  one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hab)

/-- Proposition 4.9. -/
theorem rowsFree : RowsFree := by
  intro n hn A h0 hA
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    exact star_one h0
  have hc : hole A 0 ≤ 3 := by
    by_contra h
    push_neg at h
    refine hA fun x hx => ?_
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    exact mem_of_lt_hole (by omega) (by omega)
  have hpos := (hole_mem A 0).1
  have hmono := hole_strictMono A
  have hadd := hole_add_le A
  rcases (show hole A 0 = 1 ∨ hole A 0 = 2 ∨ hole A 0 = 3 by omega) with h1 | h2 | h3
  · obtain ⟨hsub, hZ0, hcard, hΦ⟩ := fill_holes h0 le_rfl hn (K := {1})
      (by rw [Finset.range_one, Finset.image_singleton, h1]) rfl
    refine ⟨_, hsub, hZ0, hcard, hΦ.trans ?_⟩
    have hN := hadd 0 (1 + n - 2)
    rw [Nat.zero_add, h1] at hN
    rw [confTail_hole_one (by omega)]
    exact one_div_le_one_div_nat (by omega) (by omega)
  · obtain ⟨hsub, hZ0, hcard, hΦ⟩ := fill_holes h0 le_rfl hn (K := {2})
      (by rw [Finset.range_one, Finset.image_singleton, h2]) rfl
    refine ⟨_, hsub, hZ0, hcard, hΦ.trans ?_⟩
    have hN := hadd 0 (1 + n - 2)
    rw [Nat.zero_add, h2] at hN
    rw [confTail_hole_two (by omega), show ((hole A (1 + n - 2) : ℕ) : ℝ) - 1 =
      ((hole A (1 + n - 2) - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega), Nat.cast_one]]
    exact one_div_le_one_div_nat (by omega) (by omega)
  · have hb : 4 ≤ hole A 1 := by
      have := hmono (show 0 < 1 by norm_num)
      omega
    obtain ⟨hsub, hZ0, hcard, hΦ⟩ := fill_holes h0 (r := 2) (by norm_num) hn
      (K := {3, hole A 1})
      (by rw [show Finset.range 2 = {0, 1} by decide, Finset.image_insert,
        Finset.image_singleton, h3]) rfl
    refine ⟨_, hsub, hZ0, hcard, hΦ.trans ?_⟩
    have hN := hadd 1 (n - 1)
    rw [show 1 + (n - 1) = 2 + n - 2 by omega] at hN
    set N := hole A (2 + n - 2)
    set b := hole A 1
    have hle : confTail (Finset.Icc 1 N \ {3, b}) ≤
        confTail (Finset.Icc 1 (b + (n - 1)) \ {3, b}) :=
      confTail_le_of_above _ _ _ rfl (Finset.sdiff_subset_sdiff (Finset.Icc_subset_Icc le_rfl hN)
        subset_rfl) (fun h => by
          have := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 h).1).1
          omega) fun x hx y hy => by
        obtain ⟨hxY, hxY'⟩ := Finset.mem_sdiff.1 hx
        have hy2 := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hy).1).2
        have hx1 := Finset.mem_Icc.1 (Finset.mem_sdiff.1 hxY).1
        have hxC := (Finset.mem_sdiff.1 hxY).2
        by_contra hyx
        exact hxY' (Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hx1.1, by omega⟩, hxC⟩)
    refine hle.trans ((confTail_two_holes hb).trans (le_of_eq ?_))
    rw [show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by rw [Nat.cast_sub (by omega), Nat.cast_one]; ring]

end CoefficientMass
