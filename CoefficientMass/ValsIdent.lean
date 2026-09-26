/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ValsMono

/-!
# The Block Values

This module identifies the bound of Lemma 4.10 of `coefficient-mass.tex` at the block
position `c = ℓ + 1 + r`: there `W_r(c)` is the value of the block
`{ℓ + 1, …, 2ℓ + 1}` at its `r`-th hole, `2^{-(ℓ+1+r)} (2ℓ+1)! / (ℓ! r! (ℓ-r)!)
B(ℓ - r + q + 1, ℓ + r + 1)`, using `C(c - 1, k) k! (c - 1 - k)! = (c - 1)!` and
`C(c + k, k) c! k! = (c + k)!`.

## Theorems

* `pDown_mul`.
* `qUp_mul`.
* `holeW_block`.
* `hole_zero_block`.
-/

namespace CoefficientMass

theorem pDown_mul : ∀ k c : ℕ, k + 1 ≤ c →
    pDown k c * k.factorial * ((c - 1 - k).factorial : ℝ) = (c - 1).factorial := by
  intro k
  induction k with
  | zero =>
    intro c _
    rw [pDown, Finset.prod_range_zero, Nat.factorial_zero, Nat.sub_zero]
    push_cast
    ring
  | succ k ih =>
    intro c hk
    have ih' := ih c (by omega)
    rw [show c - 1 - k = c - 1 - (k + 1) + 1 by omega, Nat.factorial_succ] at ih'
    have e : ((c - 1 - (k + 1) : ℕ) : ℝ) + 1 = (c : ℝ) - 1 - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [pDown, Finset.prod_range_succ, ← pDown, Nat.factorial_succ k, ← ih']
    push_cast
    rw [e]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp

theorem qUp_mul : ∀ k c : ℕ,
    qUp k c * c.factorial * (k.factorial : ℝ) = (c + k).factorial := by
  intro k
  induction k with
  | zero =>
    intro c
    rw [qUp, Finset.prod_range_zero, Nat.factorial_zero, Nat.add_zero]
    push_cast
    ring
  | succ k ih =>
    intro c
    rw [qUp, Finset.prod_range_succ, ← qUp, Nat.factorial_succ k,
      show c + (k + 1) = c + k + 1 by ring, Nat.factorial_succ (c + k)]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    calc qUp k c * (((c : ℝ) + 1 + k) / (k + 1)) * c.factorial * (((k : ℝ) + 1) * k.factorial)
        = qUp k c * c.factorial * k.factorial * (((c : ℝ) + 1 + k) / (k + 1) * (k + 1)) := by
          ring
      _ = qUp k c * c.factorial * k.factorial * ((c : ℝ) + 1 + k) := by
          rw [div_mul_cancel₀ _ hk1]
      _ = ((c : ℝ) + k + 1) * (c + k).factorial := by
          rw [ih c]
          ring

/-- `W_{s+1}(ℓ + s + 2)` is the block value at the `(s + 1)`-th hole. -/
theorem holeW_block {ℓ q s : ℕ} (hs : s + 1 ≤ ℓ) :
    holeW ℓ q (s + 1) (ℓ + 1 + (s + 1)) =
      blockCoef ℓ (s + 1) * betaI (ℓ - (s + 1) + q) (ℓ + (s + 1)) := by
  have hp := pDown_mul s (ℓ + 1 + (s + 1)) (by omega)
  have hq := qUp_mul (ℓ - (s + 1)) (ℓ + 1 + (s + 1))
  rw [show ℓ + 1 + (s + 1) - 1 - s = ℓ + 1 by omega,
    show ℓ + 1 + (s + 1) - 1 = ℓ + s + 1 by omega,
    show ℓ + 1 + (s + 1) = ℓ + s + 1 + 1 by ring] at hp
  rw [show ℓ + 1 + (s + 1) + (ℓ - (s + 1)) = 2 * ℓ + 1 by omega,
    show ℓ + 1 + (s + 1) = ℓ + s + 1 + 1 by ring, Nat.factorial_succ (ℓ + s + 1)] at hq
  rw [holeW, blockCoef, Nat.add_sub_cancel, show ℓ + 1 + (s + 1) - 1 = ℓ + (s + 1) by omega,
    show ℓ + 1 + (s + 1) = ℓ + s + 1 + 1 by ring]
  rw [Nat.factorial_succ ℓ] at hp
  rw [Nat.factorial_succ s]
  have h1 : (s.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((ℓ - (s + 1)).factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((ℓ + s + 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : pDown s (ℓ + s + 1 + 1) = (ℓ + s + 1).factorial / (s.factorial * ((ℓ + 1) *
      ℓ.factorial) : ℝ) := by
    rw [eq_div_iff (by positivity), ← hp]
    push_cast
    ring
  have hQ : qUp (ℓ - (s + 1)) (ℓ + s + 1 + 1) = (2 * ℓ + 1).factorial /
      (((ℓ + s + 1 + 1) * (ℓ + s + 1).factorial) * (ℓ - (s + 1)).factorial : ℝ) := by
    rw [eq_div_iff (by positivity), ← hq]
    push_cast
    ring
  have h5 : (s : ℝ) + 1 ≠ 0 := by positivity
  have h6 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  have h7 : (ℓ : ℝ) + s + 1 + 1 ≠ 0 := by positivity
  have h8 : (ℓ : ℝ) + s + 1 + 1 - ℓ - 1 ≠ 0 := by
    ring_nf
    positivity
  rw [hP, hQ]
  push_cast
  field_simp
  ring

/-- At the first hole `c = ℓ + 1`: `2^{-(ℓ+1)} (ℓ + 1) B(ℓ + q + 1, ℓ + 1) C(2ℓ + 1, ℓ)` is
the block value. -/
theorem hole_zero_block (ℓ q : ℕ) :
    (1 / 2 : ℝ) ^ (ℓ + 1) * (((ℓ + 1 : ℕ) : ℝ) * betaI (ℓ + q) ℓ) * qUp ℓ (ℓ + 1) =
      blockCoef ℓ 0 * betaI (ℓ - 0 + q) (ℓ + 0) := by
  have hq := qUp_mul ℓ (ℓ + 1)
  rw [show ℓ + 1 + ℓ = 2 * ℓ + 1 by ring, Nat.factorial_succ ℓ] at hq
  have h2 : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have hQ : qUp ℓ (ℓ + 1) = (2 * ℓ + 1).factorial / (((ℓ + 1) * ℓ.factorial) *
      ℓ.factorial : ℝ) := by
    rw [eq_div_iff (by positivity), ← hq]
    push_cast
    ring
  have h5 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  rw [hQ, blockCoef]
  simp only [Nat.sub_zero, Nat.add_zero, Nat.factorial_zero]
  push_cast
  field_simp

end CoefficientMass
