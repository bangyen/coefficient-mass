/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarStep

/-!
# The Block Polynomial `r_{[2,k]}`

This module computes `|r_{[2,k]}(s)|` for the proof of Lemma 6.21 of
`coefficient-mass-rows.tex`: `|r_{[2,k]}(1)| = 1/k` and
`|r_{[2,k]}(s)| = binom(s - 2, k - 1)/k` for `s ≥ 2`, by induction on `k` with
`(k + 1)|1 - s/(k + 1)| = |k + 1 - s|` and `binom(s - 2, k) k = binom(s - 2, k - 1)(s - k - 1)`.

## Theorems

* `abs_block_eval_mul`.
-/

open Polynomial

namespace CoefficientMass

/-- `k |r_{[2,k]}(s)|` is `1` at `s = 1` and `binom(s - 2, k - 1)` for `s ≥ 2`. -/
theorem abs_block_eval_mul {k : ℕ} (hk : 1 ≤ k) {s : ℕ} (hs : 1 ≤ s) :
    |(confPolyP (Finset.Icc 2 k)).eval (s : ℝ)| * k =
      if s = 1 then 1 else ((s - 2).choose (k - 1) : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num), confPolyP, Finset.prod_empty, eval_one, abs_one,
      Nat.cast_one, mul_one]
    split_ifs
    · rfl
    · rw [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
  | succ k hk ih =>
    have hnot : k + 1 ∉ Finset.Icc 2 k := fun h => by
      have := (Finset.mem_Icc.1 h).2
      omega
    rw [confPolyP] at ih
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), confPolyP, Finset.prod_insert hnot,
      eval_mul, abs_mul, eval_add, eval_mul, eval_C, eval_X, eval_C, Nat.add_sub_cancel]
    set A := |(∏ z ∈ Finset.Icc 2 k, (C (-(1 / (z : ℝ))) * X + C 1)).eval (s : ℝ)|
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hf : |-(1 / ((k + 1 : ℕ) : ℝ)) * s + 1| * ((k + 1 : ℕ) : ℝ) = |((k : ℝ) + 1) - s| := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)), ← abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
      congr 1
      push_cast
      field_simp
      ring
    have hA0 : 0 ≤ A := abs_nonneg _
    have e : |-(1 / ((k + 1 : ℕ) : ℝ)) * s + 1| * A * ((k + 1 : ℕ) : ℝ) =
        A * |((k : ℝ) + 1) - s| := by rw [← hf]; ring
    rw [e]
    split_ifs at ih ⊢ with h1
    · subst h1
      rw [Nat.cast_one, add_sub_cancel_right, abs_of_pos hk0]
      exact ih
    · rcases le_or_gt s k with hsk | hsk
      · have h0 : (s - 2).choose (k - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have h0' : (s - 2).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [h0, Nat.cast_zero] at ih
        have hA : A = 0 := by
          rcases mul_eq_zero.1 ih with h | h
          · exact h
          · exact absurd h hk0.ne'
        rw [hA, zero_mul, h0', Nat.cast_zero]
      · have hid := Nat.choose_succ_right_eq (s - 2) (k - 1)
        rw [Nat.sub_add_cancel hk] at hid
        have hid' : ((s - 2).choose k : ℝ) * k =
            ((s - 2).choose (k - 1) : ℝ) * ((s : ℝ) - k - 1) := by
          have : ((s - 2 - (k - 1) : ℕ) : ℝ) = (s : ℝ) - k - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub hk]
            push_cast
            ring
          rw [← this]
          exact_mod_cast hid
        have hsk' : (k : ℝ) + 1 ≤ s := by exact_mod_cast hsk
        rw [abs_of_nonpos (by linarith)]
        refine (mul_right_cancel₀ hk0.ne' ?_ : A * -((k : ℝ) + 1 - s) = _)
        rw [hid', ← ih]
        ring

end CoefficientMass
