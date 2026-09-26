/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Near
import CoefficientMass.PrimeLower
import CoefficientMass.PrimeSums

/-!
# Prime Roots

This module proves Corollaries 3.5 and 3.6 of `coefficient-mass.tex`, with explicit error
terms.  Chebyshev's bounds give `(i + 1) log (i + 1) / 10 ≤ p_i - 1` and
`log p_i ≤ log (i + 1) + log log (i + 1) + 4`, where `p_i` is the `(i + 1)`-th prime, in
place of the Rosser–Schoenfeld bounds the paper cites; they suffice for errors `O(L^2)`.

## Definitions

* `primeProduct`.
* `PrimeRoots`.
* `PrimeInfimum`.

## Theorems

* `nth_prime_mono`.
* `log_nth_prime_sub_one_ge`.
* `log_nth_prime_le'`.
* `mass_primeProduct_le`.
* `primeRoots`.
* `primeInfimum`.
-/

open Polynomial

namespace CoefficientMass

/-- `P_L = ∏_{i ≤ L} (x - p_i)` over the first `L` primes. -/
noncomputable def primeProduct (L : ℕ) : ℝ[X] :=
  rootProduct ℝ fun i : Fin L => (Nat.nth Nat.Prime i : ℝ)

/-- Corollary 3.5 (prime roots): for real `r_i ≥ p_i` and a nonzero real multiple `F` with
`|f_D| ≥ 1`, `Λ(F) ≥ (L^2/2) log L - L^2`; and `Λ(P_L) ≤ (L^2/2)(log L + log log L) + 8 L^2`,
so both are `(1/2 + o(1)) L^2 log L`. -/
def PrimeRoots : Prop :=
  (∀ (L : ℕ) (r : Fin L → ℝ) (F : ℝ[X]), 1 ≤ L → Monotone r →
    (∀ i : Fin L, (Nat.nth Nat.Prime i : ℝ) ≤ r i) → F ≠ 0 → rootProduct ℝ r ∣ F →
      1 ≤ ‖F.leadingCoeff‖ →
        (L : ℝ) ^ 2 / 2 * Real.log L - L ^ 2 ≤ mass (F.map (algebraMap ℝ ℂ))) ∧
  ∀ L : ℕ, 3 ≤ L → mass ((primeProduct L).map (algebraMap ℝ ℂ)) ≤
    (L : ℝ) ^ 2 / 2 * Real.log L + (L : ℝ) ^ 2 / 2 * Real.log (Real.log L) + 8 * L ^ 2

/-- Corollary 3.6 (sharp prime-root infimum): every monic real multiple of `P_L` has mass at
least `(L^2/2)(log L + log log L) - 5 L^2`, and `P_L` itself at most
`(L^2/2)(log L + log log L) + 8 L^2`. -/
def PrimeInfimum : Prop :=
  ∀ L : ℕ, 3 ≤ L →
    (∀ Q : ℝ[X], Q.Monic →
      (L : ℝ) ^ 2 / 2 * Real.log L + (L : ℝ) ^ 2 / 2 * Real.log (Real.log L) - 5 * L ^ 2 ≤
        mass ((primeProduct L * Q).map (algebraMap ℝ ℂ))) ∧
    mass ((primeProduct L).map (algebraMap ℝ ℂ)) ≤
      (L : ℝ) ^ 2 / 2 * Real.log L + (L : ℝ) ^ 2 / 2 * Real.log (Real.log L) + 8 * L ^ 2

theorem nth_prime_mono (L : ℕ) : Monotone fun i : Fin L => (Nat.nth Nat.Prime i : ℝ) :=
  fun _ _ h => Nat.cast_le.2 ((Nat.nth_strictMono Nat.infinite_setOf_prime).monotone h)

/-- `log (p_i - 1) ≥ log (i + 1) + log log (i + 1) - log 10`. -/
theorem log_nth_prime_sub_one_ge (i : ℕ) :
    Real.log ((i : ℝ) + 1) + Real.log (Real.log ((i : ℝ) + 1)) - Real.log 10 ≤
      Real.log ((Nat.nth Nat.Prime i : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [Nat.cast_zero, zero_add, Real.log_one, Real.log_zero]
    have := Real.log_nonneg (show (1 : ℝ) ≤ (Nat.nth Nat.Prime 0 : ℝ) - 1 by linarith)
    have := Real.log_pos (show (1 : ℝ) < 10 by norm_num)
    linarith
  have hK : (2 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (1 : ℝ) ≤ i := by exact_mod_cast h0
    linarith
  have hl : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
  have h5 := nth_prime_ge_log i
  have hle : ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) / 10 ≤ (Nat.nth Nat.Prime i : ℝ) - 1 := by
    linarith
  have hpos : 0 < ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) / 10 := by positivity
  have := Real.log_le_log hpos hle
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hl.ne'] at this
  exact this

/-- `log p_i ≤ log (i + 1) + log log (i + 1) + 4` for every `i`. -/
theorem log_nth_prime_le' (i : ℕ) :
    Real.log (Nat.nth Nat.Prime i) ≤
      Real.log ((i : ℝ) + 1) + Real.log (Real.log ((i : ℝ) + 1)) + 4 := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [Nat.nth_prime_zero_eq_two, Nat.cast_zero, zero_add, Real.log_one, Real.log_zero]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  · exact log_nth_prime_le h0

/-- `Λ(P_L) ≤ (L^2/2)(log L + log log L) + 8 L^2`. -/
theorem mass_primeProduct_le {L : ℕ} (hL : 3 ≤ L) :
    mass ((primeProduct L).map (algebraMap ℝ ℂ)) ≤
      (L : ℝ) ^ 2 / 2 * Real.log L + (L : ℝ) ^ 2 / 2 * Real.log (Real.log L) + 8 * L ^ 2 := by
  have hup := mass_rootProduct_le_choose (by omega) _ (nth_prime_mono L)
    fun i => by exact_mod_cast (Nat.prime_nth_prime i).two_le
  have e := sum_range_extend (L := L) (by omega) fun i : Fin L => (Nat.nth Nat.Prime i : ℝ)
  beta_reduce at e
  rw [e] at hup
  have hC := sum_log_choose_le L
  have hsum : ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (Nat.nth Nat.Prime i) ≤
      ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) +
        ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (Real.log ((i : ℝ) + 1)) +
          4 * (L * (L + 1) / 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) * Real.log (Nat.nth Nat.Prime i)),
      ← sum_range_succ_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (log_nth_prime_le' i)
        (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
      linarith
  have h1 := sum_mul_log_le L
  have h2 := sum_mul_log_log_le hL
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
    linarith
  have hlogL1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : Real.log (Real.log L) ≤ L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log L by linarith)
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L) := Real.log_nonneg hlogL1
  have hl2 := Real.log_two_lt_d9
  have hprimeProduct : primeProduct L = rootProduct ℝ fun i : Fin L =>
      (Nat.nth Nat.Prime i : ℝ) := rfl
  rw [hprimeProduct]
  nlinarith [mul_le_mul_of_nonneg_left hlogL (by positivity : (0 : ℝ) ≤ L),
    mul_le_mul_of_nonneg_left hll (by positivity : (0 : ℝ) ≤ L)]

/-- Corollary 3.5. -/
theorem primeRoots : PrimeRoots := by
  refine ⟨fun L r F hL hmono hr hF hdvd hlead => ?_, fun L hL => mass_primeProduct_le hL⟩
  have hlm := logarithmicMass L r (F.map (algebraMap ℝ ℂ)) hmono
    (fun i => le_trans (by exact_mod_cast (Nat.prime_nth_prime i).two_le :
      (2 : ℝ) ≤ Nat.nth Nat.Prime (i : ℕ)) (hr i))
    (Polynomial.map_ne_zero hF) (by rw [rootProduct_complex]; exact Polynomial.map_dvd _ hdvd)
  rw [leadingCoeff_map, Complex.coe_algebraMap, Complex.norm_real] at hlm
  have hlog : 0 ≤ Real.log ‖F.leadingCoeff‖ := Real.log_nonneg hlead
  have hterm : ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) ≤
      ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log (r i - 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1))]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by
        have h1 := nth_prime_ge i
        have h2 : ((i : ℕ) : ℝ) + 2 ≤ Nat.nth Nat.Prime i := by exact_mod_cast h1
        linarith [hr i])) (by positivity)
  have hlow := sum_mul_log_ge hL
  have he : (L : ℝ) ^ 2 / Real.exp 1 ≤ L ^ 2 :=
    div_le_self (by positivity) (by have := Real.exp_one_gt_d9; linarith)
  have hlogL : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ L + 1) hlog,
    mul_le_mul_of_nonneg_right (show (L : ℝ) ^ 2 / 2 ≤ L * (L + 1) / 2 by nlinarith) hlogL]

/-- Corollary 3.6. -/
theorem primeInfimum : PrimeInfimum := by
  intro L hL
  refine ⟨fun Q hQ => ?_, mass_primeProduct_le hL⟩
  have hF := (rootProduct_monic (fun i : Fin L => (Nat.nth Nat.Prime i : ℝ))).mul hQ
  have hdvd : primeProduct L ∣ primeProduct L * Q := dvd_mul_right _ _
  have hlm := logarithmicMass L _ ((primeProduct L * Q).map (algebraMap ℝ ℂ))
    (nth_prime_mono L) (fun i => by exact_mod_cast (Nat.prime_nth_prime i).two_le)
    (Polynomial.map_ne_zero hF.ne_zero)
    (by rw [rootProduct_complex]; exact Polynomial.map_dvd _ hdvd)
  rw [leadingCoeff_map, show (primeProduct L * Q).leadingCoeff = 1 from hF.leadingCoeff,
    map_one, norm_one, Real.log_one, mul_zero, zero_add] at hlm
  have hterm : ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log ((i : ℝ) + 1) +
      ∑ i ∈ Finset.range L, ((i : ℝ) + 1) * Real.log (Real.log ((i : ℝ) + 1)) -
        Real.log 10 * (L * (L + 1) / 2) ≤
      ∑ i : Fin L, ((i : ℕ) + 1 : ℝ) * Real.log ((Nat.nth Nat.Prime i : ℝ) - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) *
      Real.log ((Nat.nth Nat.Prime i : ℝ) - 1)), ← sum_range_succ_eq, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (log_nth_prime_sub_one_ge i)
        (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
      linarith
  have h1 := sum_mul_log_ge (show 1 ≤ L by omega)
  have h2 := sum_mul_log_log_ge (show 2 ≤ L by omega)
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
    linarith
  have hll : Real.log (Real.log L) ≤ L := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log L by linarith)
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L) := Real.log_nonneg hlogL1
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have h10 : Real.log 10 ≤ 4 * Real.log 2 := by
    have e : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hE : (L : ℝ) ^ 2 / Real.exp 1 ≤ 0.371 * L ^ 2 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [sq_nonneg (L : ℝ)]
  have hE2 : (L : ℝ) ^ 2 / (Real.exp 1 * Real.log 2) ≤ 0.54 * L ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ 0.54 * (Real.exp 1 * Real.log 2) := by nlinarith
    nlinarith [sq_nonneg (L : ℝ)]
  have hq : (L : ℝ) * (L + 1) / 2 ≤ L ^ 2 := by nlinarith
  have h10pos : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hq h10pos,
    mul_le_mul_of_nonneg_right (show (L : ℝ) ^ 2 / 2 ≤ L * (L + 1) / 2 by nlinarith)
      (by linarith : (0 : ℝ) ≤ Real.log L),
    mul_le_mul_of_nonneg_right (show (L : ℝ) ^ 2 / 2 ≤ L * (L + 1) / 2 by nlinarith) hll0]

end CoefficientMass
