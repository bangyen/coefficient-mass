/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.NbMass
import CoefficientMass.RowPrefixRows

/-!
# Rows for Roots Between One and Two

This module proves Corollary 3.5 of `coefficient-mass-rows.tex`.  Theorem 3.3 gives
`1/(ν_k + E_k) ≤ V_r(L, k) ≤ 1/ν_k`, and `binom(s - 1, ⌊(s - 1)/2⌋) ≤ 2^{s-1}` with a geometric
sum gives `E_k(r) ≤ r^2/(4(2 - r)) (4/r^2)^k`.  For `n ≤ k`, Lemma 3.4 at the mode
`M_k = ⌊(k - 1)r/(r - 1)⌋ + 1` bounds `1/m_k(n)`.

## Definitions

* `BelowTwo`.

## Theorems

* `lossE_nonneg`.
* `lossE_le`.
* `inv_mK_le`.
* `belowTwo`.
-/

namespace CoefficientMass

/-- Corollary 3.5 of `coefficient-mass-rows.tex`: for `1 < r < 2`, `θ = 4(r - 1)/r^2`,
`1 ≤ k ≤ L`, `n = L - k + 1`, `m_k(n) = (r - 1)^k ν_k(n)` and `ε = E_k(r)/ν_k(n)`,
`1 ≥ V_r(L, k) m_k(n)/(r - 1)^k ≥ 1/(1 + ε)`, `ε ≤ r^2 θ^k/(4(2 - r) m_k(n))`, and for `n ≤ k`,
`ε ≤ r^2 (4√r/(r - 1) + 1)/(3(2 - r)) (2r(2r - 1)k/(r - 1))^{n-1}/(n - 1)! √k θ^k`. -/
def BelowTwo : Prop :=
  ∀ r : ℝ, 1 < r → r < 2 → ∀ L k : ℕ, 1 ≤ k → k ≤ L →
    rowValue r L k * ((r - 1) ^ k * nuR r k (L - k + 1)) / (r - 1) ^ k ≤ 1 ∧
    1 / (1 + lossE r k / nuR r k (L - k + 1)) ≤
      rowValue r L k * ((r - 1) ^ k * nuR r k (L - k + 1)) / (r - 1) ^ k ∧
    lossE r k / nuR r k (L - k + 1) ≤
      r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k / (4 * (2 - r) * ((r - 1) ^ k * nuR r k (L - k + 1))) ∧
    (L - k + 1 ≤ k → lossE r k / nuR r k (L - k + 1) ≤
      r ^ 2 * (4 * Real.sqrt r / (r - 1) + 1) / (3 * (2 - r)) *
        ((2 * r * (2 * r - 1) * k / (r - 1)) ^ (L - k) / (L - k).factorial) *
        Real.sqrt k * (4 * (r - 1) / r ^ 2) ^ k)

theorem lossE_nonneg {r : ℝ} (hr : 1 < r) (k : ℕ) : 0 ≤ lossE r k :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `E_k(r) ≤ r^2/(4(2 - r)) (4/r^2)^k` for `1 < r < 2`. -/
theorem lossE_le {r : ℝ} (hr : 1 < r) (hr2 : r < 2) {k : ℕ} (hk : 1 ≤ k) :
    lossE r k ≤ r ^ 2 / (4 * (2 - r)) * (4 / r ^ 2) ^ k := by
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hr0 : r ≠ 0 := by positivity
  have h2r : 2 - r ≠ 0 := (sub_pos.2 hr2).ne'
  have hq1 : 0 < 2 / r - 1 := by
    rw [div_sub_one hr0]
    exact div_pos (by linarith) (by linarith)
  calc lossE r (c + 1) ≤ ∑ s ∈ Finset.Ico 1 (2 * c + 1), 1 / 2 * (2 / r) ^ s := by
        rw [lossE, show 2 * (c + 1) - 2 = 2 * c by omega, ← Finset.Ico_add_one_right_eq_Icc]
        refine Finset.sum_le_sum fun s hs => ?_
        obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 :=
          ⟨s - 1, by have := (Finset.mem_Ico.1 hs).1; omega⟩
        rw [Nat.add_sub_cancel]
        have : ((s.choose (s / 2) : ℕ) : ℝ) ≤ 2 ^ s := by
          exact_mod_cast Nat.choose_le_two_pow _ _
        calc ((s.choose (s / 2) : ℕ) : ℝ) * (1 / r) ^ (s + 1) ≤ 2 ^ s * (1 / r) ^ (s + 1) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = 1 / 2 * (2 / r) ^ (s + 1) := by ring
    _ = 1 / 2 * (((2 / r) ^ (2 * c + 1) - (2 / r) ^ 1) / (2 / r - 1)) := by
        rw [← Finset.mul_sum, geom_sum_Ico (sub_ne_zero.1 hq1.ne') (by omega)]
    _ ≤ 1 / 2 * ((2 / r) ^ (2 * c + 1) / (2 / r - 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (sub_le_self _ (by positivity)) hq1.le) (by norm_num)
    _ = r ^ 2 / (4 * (2 - r)) * (4 / r ^ 2) ^ (c + 1) := by
        rw [show (4 : ℝ) / r ^ 2 = (2 / r) ^ 2 by ring, ← pow_mul,
          show 2 * (c + 1) = 2 * c + 1 + 1 by ring, pow_succ _ (2 * c + 1)]
        field_simp
        ring

/-- For `n ≤ k`, `1/m_k(n) ≤ (2r(2r - 1)k/(r - 1))^{n-1}/(n - 1)! · 4√k(4√r/(r - 1) + 1)/3`. -/
theorem inv_mK_le {r : ℝ} (hr : 1 < r) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hnk : n ≤ k) :
    1 / ((r - 1) ^ k * nuR r k n) ≤
      (2 * r * (2 * r - 1) * k / (r - 1)) ^ (n - 1) / (n - 1).factorial *
        (4 * (Real.sqrt k * (4 * Real.sqrt r / (r - 1) + 1)) / 3) := by
  have hr1 : 0 < r - 1 := by linarith
  set M := ⌊((k : ℝ) - 1) * r / (r - 1)⌋₊ + 1
  have hM := nbLaw_le_mode hr hk
  have hMle := nbLaw_mode_le hr hk hM
  have hP := nbLaw_mode_ge hr hk hM
  have hnodes := nbLaw_nodes_le hr (k := k) hn M
  have hs : 0 < 4 * Real.sqrt (k * r) / (r - 1) + 1 := by
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg (k * r))) hr1.le
    linarith
  have hPpos : 0 < nbLaw r k M := lt_of_lt_of_le (div_pos (by norm_num) (by linarith)) hP
  have hf : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hX : (0 : ℝ) < 2 * ((M : ℝ) + n - 1) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    linarith
  have hD : 0 < r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) :=
    mul_pos (pow_pos (by linarith) _) (pow_pos hX _)
  refine (one_div_le_one_div_of_le (div_pos (mul_pos hf hPpos) hD) hnodes).trans ?_
  rw [one_div_div]
  have hPinv : 1 / nbLaw r k M ≤ 4 * (4 * Real.sqrt (k * r) / (r - 1) + 1) / 3 := by
    rw [one_div_le hPpos (by positivity), one_div_div]
    exact hP
  have hsk : 4 * Real.sqrt (k * r) / (r - 1) + 1 ≤
      Real.sqrt k * (4 * Real.sqrt r / (r - 1) + 1) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    have h1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.2 (by exact_mod_cast hk)
    have e : Real.sqrt k * (4 * Real.sqrt r / (r - 1) + 1) =
        4 * (Real.sqrt k * Real.sqrt r) / (r - 1) + Real.sqrt k := by ring
    rw [e]
    linarith
  have hXle : (M : ℝ) + n - 1 ≤ (2 * r - 1) * k / (r - 1) := by
    have h1 : (M : ℝ) - 1 ≤ ((k : ℝ) - 1) * r / (r - 1) := by linarith
    rw [le_div_iff₀ hr1] at h1
    rw [le_div_iff₀ hr1]
    nlinarith [mul_le_mul_of_nonneg_right hnk' hr1.le]
  have hG : 0 ≤ 2 * r * (2 * r - 1) * k / (r - 1) :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (Nat.cast_nonneg _)) hr1.le
  have hDG : r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) ≤
      (2 * r * (2 * r - 1) * k / (r - 1)) ^ (n - 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (mul_pos (by linarith) hX).le ?_ _
    have := mul_le_mul_of_nonneg_left hXle (by positivity : (0 : ℝ) ≤ 2 * r)
    have e : 2 * r * (2 * r - 1) * k / (r - 1) = 2 * r * ((2 * r - 1) * k / (r - 1)) := by ring
    rw [e]
    linarith
  calc r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) / ((n - 1).factorial * nbLaw r k M)
      = r ^ (n - 1) * (2 * ((M : ℝ) + n - 1)) ^ (n - 1) / (n - 1).factorial *
          (1 / nbLaw r k M) := by rw [div_mul_div_comm, mul_one]
    _ ≤ (2 * r * (2 * r - 1) * k / (r - 1)) ^ (n - 1) / (n - 1).factorial *
          (4 * (4 * Real.sqrt (k * r) / (r - 1) + 1) / 3) :=
        mul_le_mul (div_le_div_of_nonneg_right hDG hf.le) hPinv (by positivity)
          (div_nonneg (pow_nonneg hG _) hf.le)
    _ ≤ (2 * r * (2 * r - 1) * k / (r - 1)) ^ (n - 1) / (n - 1).factorial *
          (4 * (Real.sqrt k * (4 * Real.sqrt r / (r - 1) + 1)) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (pow_nonneg hG _) hf.le)

theorem belowTwo : BelowTwo := by
  intro r hr hr2 L k hk hkL
  obtain ⟨h1, h2, h3⟩ := prefixRows r hr L k hk hkL
  have hν := nuR_pos hr hk (show 1 ≤ L - k + 1 by omega)
  have hE := lossE_nonneg hr k
  have hrk : 0 < (r - 1) ^ k := pow_pos (by linarith) k
  have h2r : 0 < 2 - r := by linarith
  have hB := lossE_le hr hr2 hk
  have hθ : (4 * (r - 1) / r ^ 2) ^ k = (4 / r ^ 2) ^ k * (r - 1) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  have e : rowValue r L k * ((r - 1) ^ k * nuR r k (L - k + 1)) / (r - 1) ^ k =
      rowValue r L k * nuR r k (L - k + 1) := by
    rw [mul_comm ((r - 1) ^ k), ← mul_assoc, mul_div_assoc, div_self hrk.ne', mul_one]
  rw [e]
  have hV := h3 k hk le_rfl
  have hE' : (r - 1) ^ k * lossE r k ≤ r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k / (4 * (2 - r)) := by
    rw [hθ]
    calc (r - 1) ^ k * lossE r k ≤ (r - 1) ^ k * (r ^ 2 / (4 * (2 - r)) * (4 / r ^ 2) ^ k) :=
          mul_le_mul_of_nonneg_left hB hrk.le
      _ = r ^ 2 * ((4 / r ^ 2) ^ k * (r - 1) ^ k) / (4 * (2 - r)) := by ring
  have hεm : lossE r k / nuR r k (L - k + 1) =
      (r - 1) ^ k * lossE r k * (1 / ((r - 1) ^ k * nuR r k (L - k + 1))) := by
    rw [mul_one_div, mul_div_mul_left _ _ hrk.ne']
  have hC : 0 ≤ r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k / (4 * (2 - r)) :=
    div_nonneg (mul_nonneg (sq_nonneg r)
      (pow_nonneg (div_nonneg (by linarith) (by positivity)) k)) (by linarith)
  have hm0 : 0 ≤ 1 / ((r - 1) ^ k * nuR r k (L - k + 1)) := (one_div_pos.2 (mul_pos hrk hν)).le
  refine ⟨?_, ?_, ?_, fun hnk => ?_⟩
  · rwa [le_div_iff₀ hν] at hV
  · rw [show 1 + lossE r k / nuR r k (L - k + 1) =
        (nuR r k (L - k + 1) + lossE r k) / nuR r k (L - k + 1) by
        rw [add_div, div_self hν.ne'],
      one_div_div, ← mul_one_div, mul_comm (rowValue r L k)]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) hν.le
  · rw [hεm]
    calc (r - 1) ^ k * lossE r k * (1 / ((r - 1) ^ k * nuR r k (L - k + 1)))
        ≤ r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k / (4 * (2 - r)) *
            (1 / ((r - 1) ^ k * nuR r k (L - k + 1))) := mul_le_mul_of_nonneg_right hE' hm0
      _ = r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k /
            (4 * (2 - r) * ((r - 1) ^ k * nuR r k (L - k + 1))) := by
          rw [div_mul_div_comm, mul_one]
  · have hm := inv_mK_le hr hk (show 1 ≤ L - k + 1 by omega) hnk
    rw [Nat.add_sub_cancel] at hm
    rw [hεm]
    calc (r - 1) ^ k * lossE r k * (1 / ((r - 1) ^ k * nuR r k (L - k + 1)))
        ≤ r ^ 2 * (4 * (r - 1) / r ^ 2) ^ k / (4 * (2 - r)) *
            ((2 * r * (2 * r - 1) * k / (r - 1)) ^ (L - k) / (L - k).factorial *
              (4 * (Real.sqrt k * (4 * Real.sqrt r / (r - 1) + 1)) / 3)) :=
          mul_le_mul hE' hm hm0 hC
      _ = r ^ 2 * (4 * Real.sqrt r / (r - 1) + 1) / (3 * (2 - r)) *
            ((2 * r * (2 * r - 1) * k / (r - 1)) ^ (L - k) / (L - k).factorial) *
            Real.sqrt k * (4 * (r - 1) / r ^ 2) ^ k := by
          field_simp

end CoefficientMass
