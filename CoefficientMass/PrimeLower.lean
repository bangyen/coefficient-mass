/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.PrimeCount

/-!
# Chebyshev's Lower Bound

This module bounds the `(i + 1)`-th prime above, for Corollaries 3.5 and 3.6 of
`coefficient-mass.tex`.  Every prime power dividing `C(2n, n)` is at most `2n`, so
`4^n ≤ (2n + 1) C(2n, n) ≤ (2n + 1) (2n)^{π(2n)}`; with `K = i + 1`, `m = ⌊log₂ K⌋` and
`n = 4 K (m + 1)` this forces `π(2n) ≥ K`, so `p_i ≤ 8 K (m + 1)` and
`log p_i ≤ log K + log log K + 4` for `K ≥ 2`.

## Theorems

* `centralBinom_le_pow`.
* `log_four_pow_le`.
* `nth_prime_le`.
* `log_nth_prime_le`.
-/

namespace CoefficientMass

/-- `C(2n, n) ≤ (2n)^{π(2n)}`. -/
theorem centralBinom_le_pow {n : ℕ} (hn : 1 ≤ n) :
    Nat.centralBinom n ≤ (2 * n) ^ (primesUpTo (2 * n)).card := by
  calc Nat.centralBinom n
      = ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p :=
        (Nat.prod_pow_factorization_centralBinom n).symm
    _ = ∏ p ∈ primesUpTo (2 * n), p ^ (Nat.centralBinom n).factorization p :=
        (Finset.prod_subset (Finset.filter_subset _ _) fun p hp hnp => by
          have hnp' : ¬ p.Prime := fun h => hnp (Finset.mem_filter.2 ⟨hp, h⟩)
          rw [Nat.factorization_eq_zero_of_non_prime _ hnp', pow_zero]).symm
    _ ≤ ∏ _p ∈ primesUpTo (2 * n), 2 * n :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p _ => by
          rw [Nat.centralBinom_eq_two_mul_choose]
          exact Nat.pow_factorization_choose_le (by omega)
    _ = (2 * n) ^ (primesUpTo (2 * n)).card := Finset.prod_const _

/-- `n log 4 ≤ log (2n + 1) + π(2n) log (2n)`. -/
theorem log_four_pow_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 ≤
      Real.log (2 * n + 1) + (primesUpTo (2 * n)).card * Real.log (2 * n) := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have h2 := Nat.mul_le_mul_left (2 * n + 1) (centralBinom_le_pow hn)
  have h : ((4 : ℝ) ^ n) ≤ (2 * n + 1) * (2 * n) ^ (primesUpTo (2 * n)).card := by
    exact_mod_cast h1.trans h2
  have hpos : (0 : ℝ) < 4 ^ n := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_log hpos h
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
  exact this

/-- `p_i ≤ 8 (i + 1) (⌊log₂ (i + 1)⌋ + 1)`. -/
theorem nth_prime_le (i : ℕ) :
    Nat.nth Nat.Prime i ≤ 8 * (i + 1) * (Nat.log 2 (i + 1) + 1) := by
  set K := i + 1 with hKdef
  set m := Nat.log 2 K
  set n := 4 * K * (m + 1) with hn
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * K * (m + 1) := ⟨_, rfl⟩
  have h2n : 2 * n = N := by rw [hn, hN]; ring
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  rw [← hN]
  by_contra hlt
  push_neg at hlt
  -- then at most `i` primes are `≤ 2n`
  have hcard : (primesUpTo (2 * n)).card ≤ i := by
    have hsub : primesUpTo (2 * n) ⊆ (primesUpTo (Nat.nth Nat.Prime i)).erase
        (Nat.nth Nat.Prime i) := fun p hp => by
      obtain ⟨hpr, hp⟩ := Finset.mem_filter.1 hp
      have := Finset.mem_range.1 hpr
      exact Finset.mem_erase.2 ⟨by omega,
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
      Nat.prime_nth_prime i⟩), card_primesUpTo_nth] at this
    omega
  have hB := log_four_pow_le hn1
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hMr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl2 := Real.log_two_gt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  -- `log K < (m + 1) log 2` and `log (m + 1) ≤ m`
  have hKlt : Real.log K < ((m : ℝ) + 1) * Real.log 2 := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) K
    have h' : (K : ℝ) < 2 ^ (m + 1) := by exact_mod_cast h
    calc Real.log K < Real.log (2 ^ (m + 1)) := Real.log_lt_log (by linarith) h'
      _ = ((m : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hm : Real.log ((m : ℝ) + 1) ≤ m := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity)
    linarith
  have hn' : ((n : ℕ) : ℝ) = 4 * K * ((m : ℝ) + 1) := by rw [hn]; norm_num
  have hlog2n : Real.log (2 * n) = 3 * Real.log 2 + Real.log K + Real.log ((m : ℝ) + 1) := by
    rw [hn', show (2 : ℝ) * (4 * K * ((m : ℝ) + 1)) = 2 ^ 3 * (K * ((m : ℝ) + 1)) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have hlog2n1 : Real.log (2 * n + 1) ≤ Real.log 2 + Real.log (2 * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hcr : ((primesUpTo (2 * n)).card : ℝ) ≤ K - 1 := by
    have : ((primesUpTo (2 * n)).card : ℝ) ≤ i := by exact_mod_cast hcard
    have hK : (K : ℝ) = i + 1 := by rw [hKdef, Nat.cast_add, Nat.cast_one]
    linarith
  have hl2n : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith)
  have hcl := mul_le_mul_of_nonneg_right hcr hl2n
  have hB' : 4 * (K : ℝ) * ((m : ℝ) + 1) * (2 * Real.log 2) ≤ Real.log (2 * n + 1) +
      (primesUpTo (2 * n)).card * Real.log (2 * n) := by
    rw [← hn', ← hlog4]
    exact hB
  rw [hlog2n] at hcl hlog2n1
  have k1 := mul_lt_mul_of_pos_left hKlt (by linarith : (0 : ℝ) < K)
  have k2 := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ K)
  have k3 : 0 ≤ (K : ℝ) * m * (7 * Real.log 2 - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hMr) (by linarith)
  have k4 := mul_le_mul_of_nonneg_right hKr hlog2.le
  nlinarith

/-- `log p_i ≤ log (i + 1) + log log (i + 1) + 4` for `i ≥ 1`. -/
theorem log_nth_prime_le {i : ℕ} (hi : 1 ≤ i) :
    Real.log (Nat.nth Nat.Prime i) ≤
      Real.log ((i : ℝ) + 1) + Real.log (Real.log ((i : ℝ) + 1)) + 4 := by
  set m := Nat.log 2 (i + 1)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hK : (2 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  have hlogK : Real.log 2 ≤ Real.log ((i : ℝ) + 1) := Real.log_le_log (by norm_num) hK
  have hlogK0 : 0 < Real.log ((i : ℝ) + 1) := by linarith
  have hmK : (m : ℝ) * Real.log 2 ≤ Real.log ((i : ℝ) + 1) := by
    have h := Nat.pow_log_le_self 2 (show i + 1 ≠ 0 by omega)
    have h' : ((2 : ℝ) ^ m) ≤ (i : ℝ) + 1 := by exact_mod_cast h
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h'
  have hp := nth_prime_le i
  have hp' : (Nat.nth Nat.Prime i : ℝ) ≤ 8 * ((i : ℝ) + 1) * ((m : ℝ) + 1) := by
    exact_mod_cast hp
  have hp0 : (0 : ℝ) < Nat.nth Nat.Prime i := by
    exact_mod_cast (Nat.prime_nth_prime i).pos
  -- `m + 1 ≤ 2 log K / log 2`
  have hm1 : (m : ℝ) + 1 ≤ 2 * Real.log ((i : ℝ) + 1) / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hlm : Real.log ((m : ℝ) + 1) ≤
      Real.log (Real.log ((i : ℝ) + 1)) + Real.log 2 - Real.log (Real.log 2) := by
    have := Real.log_le_log (by positivity) hm1
    rw [Real.log_div (by positivity) (by linarith), Real.log_mul (by norm_num) hlogK0.ne']
      at this
    linarith
  have hll2 : 1 - (Real.log 2)⁻¹ ≤ Real.log (Real.log 2) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have hinv : (Real.log 2)⁻¹ < 1.45 := by
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  calc Real.log (Nat.nth Nat.Prime i)
      ≤ Real.log (8 * ((i : ℝ) + 1) * ((m : ℝ) + 1)) := Real.log_le_log hp0 hp'
    _ = Real.log 8 + Real.log ((i : ℝ) + 1) + Real.log ((m : ℝ) + 1) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
          (by positivity)]
    _ ≤ Real.log ((i : ℝ) + 1) + Real.log (Real.log ((i : ℝ) + 1)) + 4 := by
        rw [hl8]
        linarith

end CoefficientMass
