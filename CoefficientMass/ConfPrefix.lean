/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ConfDelR

/-!
# Prefix Values at a Root `r > 1`

This module completes Lemma 2.3 of `coefficient-mass-rows.tex`.  With `x = 1/r` and
`a = x / (1 - x) = 1/(r - 1)`, the rising products satisfy `(1 - x)^{k + 1} S[q_k] = k!`, and
since `|r_{[1, ℓ]}(ℓ + 1 + t)| = q_ℓ(t) / ℓ!` this gives `Φ_r([1, ℓ]) = a^{ℓ + 1}`.  Deleting
the largest element repeatedly then gives `Φ_r(Z) ≤ Φ_r(Z ∩ [1, t])` for `r ≥ 2`, where
`max(1, a) = 1`, and `Φ_r(Z) ≤ a^{|Z| + 1}` for `r ≤ 2`, where `max(1, a) = a`.

## Definitions

* `ConfDeleteR`.

## Theorems

* `geomSum_risingP_Icc`.
* `prod_Icc_cast`.
* `image_Icc_reflect`.
* `rowPhi_prefix`.
* `rowPhi_le_filter`.
* `rowPhi_le_pow`.
* `confDeleteR`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 2.3 of `coefficient-mass-rows.tex`: for `r > 1` and `a = 1/(r - 1)`,
`Φ_r([1, ℓ]) = a^{ℓ + 1}`; `Φ_r(Z) ≤ max(1, a) Φ_r(Z \ {max Z})` for nonempty finite
`Z ⊂ ℕ_{>0}`; so `Φ_r(Z) ≤ Φ_r(Z ∩ [1, t])` when `r ≥ 2` and `Φ_r(Z) ≤ a^{|Z| + 1}` when
`r ≤ 2`. -/
def ConfDeleteR : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ ℓ : ℕ, rowPhi r (confPolyP (Finset.Icc 1 ℓ)) = (1 / (r - 1)) ^ (ℓ + 1)) ∧
    (∀ (Z : Finset ℕ) (hne : Z.Nonempty), 0 ∉ Z → rowPhi r (confPolyP Z) ≤
      max 1 (1 / (r - 1)) * rowPhi r (confPolyP (Z.erase (Z.max' hne)))) ∧
    (2 ≤ r → ∀ (Z : Finset ℕ) (t : ℕ), 0 ∉ Z →
      rowPhi r (confPolyP Z) ≤ rowPhi r (confPolyP (Z.filter (· ≤ t)))) ∧
    (r ≤ 2 → ∀ Z : Finset ℕ, 0 ∉ Z → rowPhi r (confPolyP Z) ≤ (1 / (r - 1)) ^ (Z.card + 1))

/-- `(1 - x)^{k + 1} S[q_k] = k!`. -/
theorem geomSum_risingP_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (1 - x) ^ (k + 1) * geomSum x (risingP (Finset.Icc 1 k)) = k.factorial := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num), risingP, Finset.prod_empty, geomSum]
    simp only [eval_one, one_mul]
    rw [tsum_geometric_of_lt_one hx0 hx1, zero_add, pow_one,
      mul_inv_cancel₀ (by linarith : (1 : ℝ) - x ≠ 0), Nat.factorial_zero, Nat.cast_one]
  | succ k ih =>
    have e : risingP (Finset.Icc 1 (k + 1)) =
        X * risingP (Finset.Icc 1 k) + C ((k : ℝ) + 1) * risingP (Finset.Icc 1 k) := by
      rw [risingP, Finset.prod_Icc_succ_top (by omega), ← risingP]
      push_cast
      ring
    have h := geomSum_X_mul_risingP hx0 hx1 k
    rw [e, geomSum_add hx0 hx1, geomSum_C_mul, Nat.factorial_succ, Nat.cast_mul, ← ih]
    push_cast
    linear_combination (1 - x) ^ (k + 1) * h

theorem prod_Icc_cast (ℓ : ℕ) : ∏ w ∈ Finset.Icc 1 ℓ, (w : ℝ) = ℓ.factorial := by
  induction ℓ with
  | zero => rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one]
  | succ ℓ ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul, mul_comm]

theorem image_Icc_reflect (ℓ : ℕ) :
    (Finset.Icc 1 ℓ).image (fun w => ℓ + 1 - w) = Finset.Icc 1 ℓ := by
  ext y
  rw [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have := Finset.mem_Icc.1 hw
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨ℓ + 1 - y, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩

/-- `Φ_r([1, ℓ]) = a^{ℓ + 1}`. -/
theorem rowPhi_prefix {r : ℝ} (hr : 1 < r) (ℓ : ℕ) :
    rowPhi r (confPolyP (Finset.Icc 1 ℓ)) = (1 / (r - 1)) ^ (ℓ + 1) := by
  have hx0 : 0 < 1 / r := by positivity
  have hx1 : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr
  have hxa : 1 / r / (1 - 1 / r) = 1 / (r - 1) := by
    have : r - 1 ≠ 0 := by linarith
    have : r ≠ 0 := by positivity
    field_simp
  have hpos : ∀ w ∈ Finset.Icc 1 ℓ, 0 < w := fun w hw => (Finset.mem_Icc.1 hw).1
  have hlt : ∀ w ∈ Finset.Icc 1 ℓ, w < ℓ + 1 := fun w hw =>
    Nat.lt_succ_of_le (Finset.mem_Icc.1 hw).2
  have hv : ∀ t : ℕ, |confPoly (Finset.Icc 1 ℓ) (t + (ℓ + 1))| =
      (risingP (Finset.Icc 1 ℓ)).eval (t : ℝ) / ℓ.factorial := fun t => by
    rw [abs_confPoly_add hpos hlt, image_Icc_reflect, prod_Icc_cast]
  have hzero : ∀ d ∈ Finset.range ℓ,
      |confPoly (Finset.Icc 1 ℓ) (d + 1)| * (1 / r) ^ (d + 1) = 0 := fun d hd => by
    have hd := Finset.mem_range.1 hd
    rw [confPoly, Finset.prod_eq_zero (i := d + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      (by rw [div_self (by positivity), sub_self]), abs_zero, zero_mul]
  have hall := (summable_conf hr (Finset.Icc 1 ℓ)).sum_add_tsum_nat_add ℓ
  rw [Finset.sum_eq_zero hzero, zero_add] at hall
  have htail : ∀ t : ℕ, |confPoly (Finset.Icc 1 ℓ) (t + ℓ + 1)| * (1 / r) ^ (t + ℓ + 1) =
      (1 / r) ^ (ℓ + 1) / ℓ.factorial *
        ((risingP (Finset.Icc 1 ℓ)).eval (t : ℝ) * (1 / r) ^ t) := fun t => by
    rw [add_assoc, hv]
    ring
  have hS := geomSum_risingP_Icc hx0.le hx1 ℓ
  rw [geomSum] at hS
  have hf : (0 : ℝ) < ℓ.factorial := by exact_mod_cast ℓ.factorial_pos
  have h1x : (1 - 1 / r) ^ (ℓ + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  have hS' : ∑' t : ℕ, (risingP (Finset.Icc 1 ℓ)).eval (t : ℝ) * (1 / r) ^ t =
      ℓ.factorial / (1 - 1 / r) ^ (ℓ + 1) := by
    rw [eq_div_iff h1x, ← hS, mul_comm]
  rw [rowPhi_conf, ← hall, tsum_congr htail, tsum_mul_left, hS', div_mul_div_comm,
    mul_comm ((1 / r) ^ (ℓ + 1)), mul_div_mul_left _ _ hf.ne', ← div_pow, hxa]

/-- For `r ≥ 2`, `Φ_r(Z) ≤ Φ_r(Z ∩ [1, t])`. -/
theorem rowPhi_le_filter {r : ℝ} (hr : 2 ≤ r) (t : ℕ) :
    ∀ (n : ℕ) (Z : Finset ℕ), Z.card = n → 0 ∉ Z →
      rowPhi r (confPolyP Z) ≤ rowPhi r (confPolyP (Z.filter (· ≤ t))) := by
  have hm : max 1 (1 / (r - 1)) = 1 :=
    max_eq_left (by rw [div_le_one (by linarith)]; linarith)
  intro n
  induction n with
  | zero =>
    intro Z hZ _
    rw [Finset.card_eq_zero.1 hZ, Finset.filter_empty]
  | succ n ih =>
    intro Z hZ h0
    have hne : Z.Nonempty := Finset.card_pos.1 (by omega)
    by_cases hmax : Z.max' hne ≤ t
    · rw [Finset.filter_true_of_mem fun w hw => (Z.le_max' w hw).trans hmax]
    have h1 := rowPhi_erase_max (r := r) (by linarith) hne h0
    rw [hm, one_mul] at h1
    have h0' : 0 ∉ Z.erase (Z.max' hne) := fun h => h0 (Finset.mem_of_mem_erase h)
    have h2 := ih _ (by rw [Finset.card_erase_of_mem (Z.max'_mem hne), hZ, Nat.add_sub_cancel])
      h0'
    have hnot : Z.max' hne ∉ Z.filter (· ≤ t) := fun h => hmax (Finset.mem_filter.1 h).2
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hnot] at h2
    exact h1.trans h2

/-- For `1 < r ≤ 2`, `Φ_r(Z) ≤ a^{|Z| + 1}`. -/
theorem rowPhi_le_pow {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) :
    ∀ (n : ℕ) (Z : Finset ℕ), Z.card = n → 0 ∉ Z →
      rowPhi r (confPolyP Z) ≤ (1 / (r - 1)) ^ (n + 1) := by
  have hm : max 1 (1 / (r - 1)) = 1 / (r - 1) :=
    max_eq_right (by rw [le_div_iff₀ (by linarith)]; linarith)
  have ha : 0 ≤ 1 / (r - 1) := by
    have : 0 < r - 1 := by linarith
    positivity
  intro n
  induction n with
  | zero =>
    intro Z hZ _
    rw [Finset.card_eq_zero.1 hZ, ← Finset.Icc_eq_empty (show ¬ 1 ≤ 0 by norm_num),
      rowPhi_prefix hr]
  | succ n ih =>
    intro Z hZ h0
    have hne : Z.Nonempty := Finset.card_pos.1 (by omega)
    have h1 := rowPhi_erase_max hr hne h0
    rw [hm] at h1
    have h2 := ih _ (by rw [Finset.card_erase_of_mem (Z.max'_mem hne), hZ, Nat.add_sub_cancel])
      fun h => h0 (Finset.mem_of_mem_erase h)
    calc rowPhi r (confPolyP Z) ≤ 1 / (r - 1) * (1 / (r - 1)) ^ (n + 1) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 ha)
      _ = (1 / (r - 1)) ^ (n + 1 + 1) := by ring

theorem confDeleteR : ConfDeleteR := fun _ hr =>
  ⟨rowPhi_prefix hr, fun _ hne h0 => rowPhi_erase_max hr hne h0,
    fun hr2 Z t h0 => rowPhi_le_filter hr2 t _ Z rfl h0,
    fun hr2 Z h0 => rowPhi_le_pow hr hr2 _ Z rfl h0⟩

end CoefficientMass
