/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Interp

/-!
# Signs in the Displaced Step

The displaced step of Theorem 2.2 in `coefficient-mass.tex` removes the
largest zero `z` of `Z` and the largest node.  With `Z' = Z \ {z}` and
`A = {0} ∪ Z'`, the sum `F` on the smaller nodes has `F_0 = 1` and zeros `Z'`,
and `G` on all nodes vanishes on `A` with `G_z = 1`.  This module records
their sign patterns and proves the paper's bound `σ ≤ G_z / F̂_z` by the sign
of `G - τ F̂`, where the paper argues asymptotically.

## Theorems

* `ne_zero_of_expSum_eq_one`.
* `sign_of_certificate`.
* `sign_before_top`.
* `pos_beyond`.
* `theta_bound`.
-/

namespace CoefficientMass

theorem ne_zero_of_expSum_eq_one {c : ℕ} {a y : Fin c → ℝ} {k : ℕ} (h : expSum a y k = 1) :
    a ≠ 0 := fun ha => by
  rw [ha] at h
  simp only [expSum, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  exact zero_ne_one h

/-- A certificate `w` with zeros `T` has the sign `(-1)^{#{τ ∈ T : τ < d}}` at `d`. -/
theorem sign_of_certificate {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (T : Finset ℕ) (hT : T.card + 1 = c) (h0 : 0 ∉ T)
    (ha : IsCertificate a y T) {d : ℕ} (hd : 0 < d) (hdT : d ∉ T) :
    0 < (-1) ^ (T.filter (· < d)).card * expSum a y d := by
  have h := sign_between a y hy hpos (ne_zero_of_expSum_eq_one ha.1) T hT ha.2 h0 hdT hd
  rw [ha.1, one_mul] at h
  have hf : T.filter (fun τ => 0 < τ ∧ τ < d) = T.filter (· < d) :=
    Finset.filter_congr fun τ hτ =>
      ⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero fun h' => h0 (h' ▸ hτ), h⟩⟩
  rwa [hf] at h

/-- A sum with zeros `T` below `z` and value one at `z` has the sign
`(-1)^{#{τ ∈ T : d < τ}}` at `d < z`. -/
theorem sign_before_top {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (T : Finset ℕ) (hT : T.card + 1 = c)
    (hzero : ∀ τ ∈ T, expSum a y τ = 0) {z : ℕ} (hz : expSum a y z = 1) (hzT : ∀ τ ∈ T, τ < z)
    {d : ℕ} (hdT : d ∉ T) (hdz : d < z) :
    0 < (-1) ^ (T.filter (d < ·)).card * expSum a y d := by
  have h := sign_between a y hy hpos (ne_zero_of_expSum_eq_one hz) T hT hzero hdT
    (fun h => lt_irrefl _ (hzT z h)) hdz
  rw [hz, mul_one] at h
  have hf : T.filter (fun τ => d < τ ∧ τ < z) = T.filter (d < ·) :=
    Finset.filter_congr fun τ hτ => ⟨fun h => h.1, fun h => ⟨h, hzT τ hτ⟩⟩
  rwa [hf] at h

/-- Past all its zeros, a sum with value one at `z` is positive. -/
theorem pos_beyond {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (T : Finset ℕ) (hT : T.card + 1 = c)
    (hzero : ∀ τ ∈ T, expSum a y τ = 0) {z : ℕ} (hz : expSum a y z = 1) (hzT : ∀ τ ∈ T, τ < z)
    {d : ℕ} (hdT : ∀ τ ∈ T, τ < d) : 0 < expSum a y d := by
  rcases lt_trichotomy d z with hlt | rfl | hgt
  · have h := sign_before_top a y hy hpos T hT hzero hz hzT
      (fun h => lt_irrefl _ (hdT d h)) hlt
    rwa [Finset.filter_false_of_mem fun τ hτ => not_lt.2 (hdT τ hτ).le, Finset.card_empty,
      pow_zero, one_mul] at h
  · rw [hz]
    exact one_pos
  · have h := sign_between a y hy hpos (ne_zero_of_expSum_eq_one hz) T hT hzero
      (fun h => lt_irrefl _ (hzT z h)) (fun h => lt_irrefl _ (hdT d h)) hgt
    rwa [Finset.filter_false_of_mem fun τ hτ h' => lt_asymm h'.1 (hzT τ hτ), Finset.card_empty,
      pow_zero, one_mul, hz, one_mul] at h

/-- The paper's `σ ≤ G_z / F̂_z`: with `F̂ = η F`, `η = (-1)^{|Z'|}` and
`m = max A`, one has `G_{m+1} · η F_z ≤ η F_{m+1}`. -/
theorem theta_bound {n : ℕ} (y : Fin (n + 1) → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (Z : Finset ℕ) {z : ℕ} (hz : z ∈ Z) (hzmax : ∀ τ ∈ Z, τ ≤ z)
    (h0 : 0 ∉ Z) (hcard : Z.card = n) (aF : Fin n → ℝ)
    (hF : IsCertificate aF (fun i => y i.castSucc) (Z.erase z)) (aG : Fin (n + 1) → ℝ)
    (hG0 : ∀ k ∈ insert 0 (Z.erase z), expSum aG y k = 0) (hGz : expSum aG y z = 1)
    {m : ℕ} (hm : m ∈ insert 0 (Z.erase z)) (hmmax : ∀ τ ∈ Z.erase z, τ ≤ m)
    (hmz : m < z) (hμ : 0 < (-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) z) :
    expSum aG y (m + 1) * ((-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) z) ≤
      (-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) (m + 1) := by
  set η : ℝ := (-1) ^ (Z.erase z).card with hη
  set F := expSum aF (fun i => y i.castSucc) with hFdef
  set μ := η * F z with hμdef
  rcases eq_or_ne z (m + 1) with hzm | hzm
  · rw [← hzm, hGz, one_mul]
  have hηη : η * η = 1 := neg_one_pow_mul_self _
  have hΘ : ∀ d, expSum (fun i => aG i - η / μ * Fin.snoc (α := fun _ => ℝ) aF 0 i) y d =
      expSum aG y d - η / μ * F d := fun d => by
    rw [expSum_sub, expSum_mul_left, expSum_snoc]
  have hΘ0 : expSum (fun i => aG i - η / μ * Fin.snoc (α := fun _ => ℝ) aF 0 i) y 0 =
      -(η / μ) := by
    rw [hΘ, hG0 0 (Finset.mem_insert_self _ _), hFdef, hF.1]
    ring
  have hne : (fun i => aG i - η / μ * Fin.snoc (α := fun _ => ℝ) aF 0 i) ≠ 0 := fun h => by
    rw [h] at hΘ0
    simp only [expSum, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hΘ0
    exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hμ.ne' (neg_eq_zero.1 hΘ0.symm)
  have hzeros : ∀ τ ∈ Z, expSum (fun i => aG i - η / μ * Fin.snoc (α := fun _ => ℝ) aF 0 i)
      y τ = 0 := fun τ hτ => by
    rw [hΘ]
    rcases eq_or_ne τ z with rfl | hτz
    · rw [hGz, div_mul_eq_mul_div, ← hμdef, div_self hμ.ne', sub_self]
    · have hτ' := Finset.mem_erase.2 ⟨hτz, hτ⟩
      rw [hG0 τ (Finset.mem_insert_of_mem hτ'), hFdef, hF.2 τ hτ', mul_zero, sub_zero]
  have hm1 : m + 1 ∉ Z := fun h => by
    rcases eq_or_ne (m + 1) z with h' | h'
    · exact hzm h'.symm
    · have := hmmax _ (Finset.mem_erase.2 ⟨h', h⟩)
      omega
  have h := sign_between _ y hy hpos hne Z (by rw [hcard]) hzeros h0 hm1 (Nat.succ_pos m)
  have hcnt : Z.filter (fun τ => 0 < τ ∧ τ < m + 1) = Z.erase z := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hτ, _, h2⟩
      exact ⟨by omega, hτ⟩
    · rintro ⟨hτz, hτ⟩
      exact ⟨hτ, Nat.pos_of_ne_zero fun h' => h0 (h' ▸ hτ),
        Nat.lt_succ_of_le (hmmax τ (Finset.mem_erase.2 ⟨hτz, hτ⟩))⟩
  rw [hcnt, hΘ0, hΘ (m + 1), ← hη] at h
  have hX : expSum aG y (m + 1) - η / μ * F (m + 1) < 0 := by
    have h2 : η * (-(η / μ) * (expSum aG y (m + 1) - η / μ * F (m + 1))) =
        -((η * η) * (expSum aG y (m + 1) - η / μ * F (m + 1)) / μ) := by ring
    rw [h2, hηη, one_mul, neg_pos] at h
    exact (div_neg_iff.1 h).elim (fun h => absurd h.2 (not_lt.2 hμ.le)) fun h => h.1
  have h3 : (expSum aG y (m + 1) - η / μ * F (m + 1)) * μ =
      expSum aG y (m + 1) * μ - η * F (m + 1) := by
    field_simp
  nlinarith [mul_neg_of_neg_of_pos hX hμ]

end CoefficientMass
