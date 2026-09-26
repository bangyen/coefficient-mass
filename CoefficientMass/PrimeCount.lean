/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

/-!
# Chebyshev's Upper Bound

This module prepares Corollaries 3.5 and 3.6 of `coefficient-mass.tex`, which use the size
of the `n`-th prime.  From `∏_{p ≤ n} p ≤ 4^n`, the primes in `(√n, n]` number at most
`2 n log 4 / log n`, so `π(n) ≤ 5 n / log n`; hence the `(i + 1)`-th prime `p_i` has
`p_i ≥ (i + 1) log (i + 1) / 5`, besides the trivial `p_i ≥ i + 2`.

## Definitions

* `primesUpTo`.

## Theorems

* `nth_prime_ge`.
* `card_primesUpTo_nth`.
* `sum_log_primes_le`.
* `sqrt_mul_log_le`.
* `card_primesUpTo_le`.
* `nth_prime_ge_log`.
-/

namespace CoefficientMass

/-- The primes `p ≤ n`. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

theorem nth_prime_ge (i : ℕ) : i + 2 ≤ Nat.nth Nat.Prime i := by
  induction i with
  | zero => rw [Nat.nth_prime_zero_eq_two]
  | succ i ih =>
    have : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self i)
    omega

/-- There are `i + 1` primes up to the `(i + 1)`-th prime. -/
theorem card_primesUpTo_nth (i : ℕ) : (primesUpTo (Nat.nth Nat.Prime i)).card = i + 1 := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have h : Nat.count Nat.Prime (Nat.nth Nat.Prime (i + 1)) = i + 1 :=
    Nat.count_nth_of_infinite Nat.infinite_setOf_prime (i + 1)
  rw [Nat.count_eq_card_filter_range] at h
  have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) := hmono (Nat.lt_succ_self i)
  have hsub : primesUpTo (Nat.nth Nat.Prime i) =
      (Finset.range (Nat.nth Nat.Prime (i + 1))).filter Nat.Prime := by
    ext p
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hpr⟩
      exact ⟨by omega, hpr⟩
    · rintro ⟨hp, hpr⟩
      refine ⟨Nat.lt_succ_of_le (not_lt.1 fun h' => ?_), hpr⟩
      obtain ⟨j, hj⟩ : ∃ j, Nat.nth Nat.Prime j = p :=
        ⟨Nat.count Nat.Prime p, Nat.nth_count hpr⟩
      rw [← hj] at h' hp
      have h1 := hmono.lt_iff_lt.1 h'
      have h2 := hmono.lt_iff_lt.1 hp
      omega
  rw [hsub, h]

/-- `∑_{p ≤ n} log p ≤ n log 4`. -/
theorem sum_log_primes_le (n : ℕ) :
    ∑ p ∈ primesUpTo n, Real.log p ≤ n * Real.log 4 := by
  have h := primorial_le_4_pow n
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have hlog := Real.log_le_log hpos (show (primorial n : ℝ) ≤ 4 ^ n by exact_mod_cast h)
  rw [Real.log_pow, primorial, Nat.cast_prod, Real.log_prod fun p hp =>
    Nat.cast_ne_zero.2 (Finset.mem_filter.1 hp).2.ne_zero] at hlog
  exact hlog

/-- `√n log n ≤ 2 n`. -/
theorem sqrt_mul_log_le (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x * Real.log x ≤ 2 * x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.log_zero, mul_zero, mul_zero]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 h
  have hl : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt hx]
  have := Real.log_le_sub_one_of_pos hs
  calc Real.sqrt x * Real.log x = 2 * (Real.sqrt x * Real.log (Real.sqrt x)) := by rw [hl]; ring
    _ ≤ 2 * (Real.sqrt x * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hs.le) (by norm_num)
    _ = 2 * x := by rw [Real.mul_self_sqrt hx]

/-- Chebyshev: `π(n) log n ≤ 5 n`. -/
theorem card_primesUpTo_le (n : ℕ) : ((primesUpTo n).card : ℝ) * Real.log n ≤ 5 * n := by
  set t := Nat.sqrt n
  set S := primesUpTo n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- the primes up to `√n`
  have h1 : ((S.filter (· ≤ t)).card : ℝ) ≤ Real.sqrt n := by
    have hc : (S.filter (· ≤ t)).card ≤ t := by
      have := Finset.card_le_card (show S.filter (· ≤ t) ⊆ Finset.Icc 1 t from fun p hp => by
        obtain ⟨hpS, hpt⟩ := Finset.mem_filter.1 hp
        exact Finset.mem_Icc.2 ⟨(Finset.mem_filter.1 hpS).2.one_lt.le, hpt⟩)
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (Nat.cast_le.2 hc).trans (Real.nat_sqrt_le_real_sqrt)
  -- the primes above `√n` have `log n < 2 log p`
  have h2 : ((S.filter (fun p => ¬ p ≤ t)).card : ℝ) * Real.log n ≤ 2 * (n * Real.log 4) := by
    have hle : ∑ p ∈ S.filter (fun p => ¬ p ≤ t), Real.log p ≤ n * Real.log 4 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ =>
        Real.log_natCast_nonneg p).trans (sum_log_primes_le n)
    have hbig : ∀ p ∈ S.filter (fun p => ¬ p ≤ t), Real.log n ≤ 2 * Real.log p := fun p hp => by
      obtain ⟨hpS, hpt⟩ := Finset.mem_filter.1 hp
      have hp2 := (Finset.mem_filter.1 hpS).2.two_le
      have hsq : n < p * p := (Nat.lt_succ_sqrt n).trans_le
        (Nat.mul_le_mul (by omega) (by omega))
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact mul_nonneg (by norm_num) (Real.log_natCast_nonneg p)
      have e : Real.log ((p : ℝ) ^ 2) = 2 * Real.log p := by
        rw [Real.log_pow]
        push_cast
        ring
      rw [← e]
      exact Real.log_le_log (by exact_mod_cast h0) (by rw [sq]; exact_mod_cast hsq.le)
    have := Finset.sum_le_sum hbig
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at this
    linarith
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun p => p ≤ t)
  have hsq := sqrt_mul_log_le n hn0
  have h4 : Real.log 4 < 1.39 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hS : (S.card : ℝ) = (S.filter (· ≤ t)).card + (S.filter (fun p => ¬ p ≤ t)).card := by
    exact_mod_cast hsplit.symm
  rw [hS, add_mul]
  nlinarith [mul_le_mul_of_nonneg_right h1 hlogn]

/-- `(i + 1) log (i + 1) ≤ 5 p_i` for the `(i + 1)`-th prime `p_i`. -/
theorem nth_prime_ge_log (i : ℕ) :
    ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) ≤ 5 * Nat.nth Nat.Prime i := by
  have h := card_primesUpTo_le (Nat.nth Nat.Prime i)
  rw [card_primesUpTo_nth] at h
  have hp := nth_prime_ge i
  have hK : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hle : (i : ℝ) + 1 ≤ Nat.nth Nat.Prime i := by exact_mod_cast (show i + 1 ≤ _ by omega)
  push_cast at h
  calc ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1)
      ≤ ((i : ℝ) + 1) * Real.log (Nat.nth Nat.Prime i) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hK hle) hK.le
    _ ≤ 5 * Nat.nth Nat.Prime i := h

end CoefficientMass
