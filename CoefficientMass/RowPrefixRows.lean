/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowOmega

/-!
# Rows Through Prefix Sets

This module proves Theorem 3.3 of `coefficient-mass-rows.tex`:
`1/(ν_k(n) + E_k(r)) ≤ 1/Ω_k(n) ≤ V_r(L, k) ≤ min_{i ≤ k} 1/ν_i(n)` with `n = L - k + 1`.
The upper bound exempts the prefix `[1, i - 1]` and a far block; the lower bounds compare
every exempted set with the weight `W_k` and use integer zero sets at least `k`.

## Definitions

* `PrefixRows`.

## Theorems

* `omegaR_le`.
* `omegaR_pos`.
* `prefixRows`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 3.3 of `coefficient-mass-rows.tex`: for `r > 1`, `1 ≤ k ≤ L` and
`n = L - k + 1`, `1/(ν_k(n) + E_k(r)) ≤ 1/Ω_k(n) ≤ V_r(L, k)` and
`V_r(L, k) ≤ 1/ν_i(n)` for every `1 ≤ i ≤ k`. -/
def PrefixRows : Prop :=
  ∀ r : ℝ, 1 < r → ∀ L k : ℕ, 1 ≤ k → k ≤ L →
    1 / (nuR r k (L - k + 1) + lossE r k) ≤ 1 / omegaR r k (L - k + 1) ∧
    1 / omegaR r k (L - k + 1) ≤ rowValue r L k ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k → rowValue r L k ≤ 1 / nuR r i (L - k + 1)

/-- `Ω_k(n) ≤ ν_k(n) + E_k(r)`. -/
theorem omegaR_le {r : ℝ} (hr : 1 < r) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    omegaR r k n ≤ nuR r k n + lossE r k := by
  classical
  have hx : 0 < 1 / r := by positivity
  have hvan : ∀ s, s < k → prefixWeight r k s = 0 := fun s hs => by
    unfold prefixWeight
    split_ifs with h
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    · rfl
  have hpos : ∀ s, k ≤ s → 0 < prefixWeight r k s := fun s hs => by
    rw [prefixWeight, if_pos (by omega)]
    exact mul_pos (by exact_mod_cast Nat.choose_pos (by omega)) (by positivity)
  have hν := intZerosInf (prefixWeight r k) k n hk hn hvan hpos
    (summable_weight_pow hr (prefixWeight_le hr k) (n - 1))
  haveI : Nonempty {Y : Finset ℕ // (∀ y ∈ Y, k ≤ y) ∧ Y.card + 1 = n} :=
    ⟨⟨Finset.Icc k (k + n - 2), fun y hy => (Finset.mem_Icc.1 hy).1, by
      rw [Nat.card_Icc]; omega⟩⟩
  rw [nuR, hν, ← sub_le_iff_le_add]
  refine le_ciInf fun Y => ?_
  obtain ⟨Y, hYk, hYc⟩ := Y
  change _ ≤ ∑' s : ℕ, prefixWeight r k s * |(confPolyP Y).eval (s : ℝ)|
  have hY0 : 0 ∉ Y := fun h => by have := hYk 0 h; omega
  have hadm := confPolyP_admissible (L := n) hY0 (by omega)
  have hΩ : omegaR r k n ≤ ∑' s : ℕ, omegaWeight r k s * |(confPolyP Y).eval (s : ℝ)| :=
    ciInf_le ⟨0, by
      rintro _ ⟨p, rfl⟩
      exact tsum_nonneg fun s => mul_nonneg (omegaWeight_le hr k s).1 (abs_nonneg _)⟩
      (⟨confPolyP Y, hadm.1, hadm.2.1⟩ : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})
  set E : ℕ → ℝ := fun s => if s ∈ Finset.Icc 1 (2 * k - 2) then
    ((s - 1).choose ((s - 1) / 2) : ℝ) * (1 / r) ^ s else 0
  have hE : ∑' s, E s = lossE r k := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (2 * k - 2)) fun s hs => if_neg hs, lossE]
    exact Finset.sum_congr rfl fun s hs => if_pos hs
  have hEs : Summable E := summable_of_ne_finset_zero (s := Finset.Icc 1 (2 * k - 2))
    fun s hs => if_neg hs
  have hbound : ∀ s : ℕ, |(confPolyP Y).eval (s : ℝ)| ≤ 1 * (1 + (s : ℝ)) ^ (n - 1) :=
      fun s => by
    rw [one_mul, show n - 1 = Y.card by omega]
    exact abs_confPolyP_le_pow hY0 (Nat.cast_nonneg s)
  have hPs := summable_weighted (fun s => (prefixWeight_le hr k s).1)
    (summable_weight_pow hr (prefixWeight_le hr k) (n - 1)) 1 hbound
  have hOs := summable_weighted (fun s => (omegaWeight_le hr k s).1)
    (summable_weight_pow hr (omegaWeight_le hr k) (n - 1)) 1 hbound
  have hterm : ∀ s : ℕ, omegaWeight r k s * |(confPolyP Y).eval (s : ℝ)| ≤
      E s + prefixWeight r k s * |(confPolyP Y).eval (s : ℝ)| := fun s => by
    have hP0 := mul_nonneg (prefixWeight_le hr k s).1 (abs_nonneg ((confPolyP Y).eval (s : ℝ)))
    rcases Nat.eq_zero_or_pos s with h0 | h1
    · have hE0 : E s = 0 := if_neg fun h => by have := (Finset.mem_Icc.1 h).1; omega
      rw [hE0, zero_add, omegaWeight, if_neg (by omega), zero_mul]
      exact hP0
    rcases le_or_gt s (2 * k - 2) with hs | hs
    · -- a first position: `W_k(s) ≤ binom(s - 1, ⌊(s - 1)/2⌋)` and `|r_Y(s)| ≤ 1`
      have hEs' : E s = ((s - 1).choose ((s - 1) / 2) : ℝ) * (1 / r) ^ s :=
        if_pos (Finset.mem_Icc.2 ⟨by omega, hs⟩)
      have hr1 : |(confPolyP Y).eval (s : ℝ)| ≤ 1 := abs_confPolyP_le_one (Nat.cast_nonneg s)
        fun y hy => ⟨by have := hYk y hy; omega, by
          have := hYk y hy
          exact_mod_cast (show s ≤ 2 * y by omega)⟩
      have hW : (wK k s : ℝ) ≤ ((s - 1).choose ((s - 1) / 2) : ℝ) := by
        rw [wK]
        exact_mod_cast Nat.choose_le_middle _ _
      rw [hEs', omegaWeight, if_pos (show 1 ≤ s by omega)]
      have hxs : 0 ≤ (1 / r) ^ s := by positivity
      calc (wK k s : ℝ) * (1 / r) ^ s * |(confPolyP Y).eval (s : ℝ)|
          ≤ ((s - 1).choose ((s - 1) / 2) : ℝ) * (1 / r) ^ s * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hW hxs) hr1 (abs_nonneg _) (by positivity)
        _ ≤ _ := by rw [mul_one]; linarith
    · -- a later position: `W_k(s) = binom(s - 1, k - 1)`
      have hE0 : E s = 0 := if_neg fun h => by have := (Finset.mem_Icc.1 h).2; omega
      rw [hE0, zero_add, omegaWeight, prefixWeight, if_pos (show 1 ≤ s by omega),
        if_pos (show 1 ≤ s by omega), wK_eq (by omega)]
  have := Summable.tsum_le_tsum hterm hOs (hEs.add hPs)
  rw [hEs.tsum_add hPs, hE] at this
  linarith

theorem omegaR_pos {r : ℝ} (hr : 1 < r) {L k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) :
    0 < omegaR r k (L - k + 1) := by
  have h0 : 0 ∉ Finset.Icc 1 (k - 1) := fun h => by have := (Finset.mem_Icc.1 h).1; omega
  have hc : (Finset.Icc 1 (k - 1)).card + 1 = k := by rw [Nat.card_Icc]; omega
  exact (muR_pos hr h0 (by omega)).trans_le (muR_le_omegaR hr hkL h0 hc)

theorem prefixRows : PrefixRows := by
  intro r hr L k hk hkL
  have hΩ := omegaR_pos hr hk hkL
  refine ⟨one_div_le_one_div_of_le hΩ (omegaR_le hr hk (by omega)), ?_, fun i hi hik => ?_⟩
  · haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k} :=
      ⟨⟨Finset.Icc 1 (k - 1), fun h => by
        have := (Finset.mem_Icc.1 h).1
        omega, by rw [Nat.card_Icc]; omega⟩⟩
    rw [(rowValueDual r hr).1 L k hk hkL]
    refine le_ciInf fun S => ?_
    have hc : S.1.card < L := by have := S.2.2; omega
    exact one_div_le_one_div_of_le (muR_pos hr S.2.1 hc) (muR_le_omegaR hr hkL S.2.1 S.2.2)
  · have h0 : 0 ∉ Finset.Icc 1 (i - 1) := fun h => by
      have := (Finset.mem_Icc.1 h).1
      omega
    have hc : (Finset.Icc 1 (i - 1)).card = i - 1 := by rw [Nat.card_Icc]; omega
    have h := rowValue_le_base hr hk hkL h0 (by rw [hc]; omega)
    rwa [hc, show L - (k - 1 - (i - 1)) = L - k + 1 + (i - 1) by omega,
      muR_prefix hr hi (by omega)] at h

end CoefficientMass
