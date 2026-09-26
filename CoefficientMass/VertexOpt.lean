/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.VertexBasis
import Mathlib.Data.Real.Sign

/-!
# Certifying a Vertex

This module proves the sufficiency part of Lemma 6.11 of `coefficient-mass-rows.tex`.  With
`G_y = ∑_{s ∉ Z} sgn(r_Z(s)) e_y(s) r^{-s}`, if `|G_y| ≤ |e_y(y)| r^{-y}` for every
`y ∈ Z \ S`, then every admissible `q = r_Z + ∑_y c_y e_y` has
`Φ_r(q) - Φ_r(Z) ≥ ∑_y (c_y G_y + |c_y| |e_y(y)| r^{-y}) ≥ 0`, from
`|a + b| - |a| ≥ sgn(a) b + [a = 0] |b|`.

## Definitions

* `gY`.

## Theorems

* `sign_mul_add_le`.
* `summable_sign_mul`.
* `summable_zero_mul`.
* `rowPhi_sub_ge_sum`.
* `rowPhi_le_of_cert`.
-/

open Polynomial

namespace CoefficientMass

/-- `G_y = ∑_{s ≥ 1} sgn(r_Z(s)) e_y(s) r^{-s}` (the terms at `s ∈ Z` vanish). -/
noncomputable def gY (r : ℝ) (Z : Finset ℕ) (y : ℕ) : ℝ :=
  ∑' d : ℕ, Real.sign ((confPolyP Z).eval ((d + 1 : ℕ) : ℝ)) * (eY Z y).eval ((d + 1 : ℕ) : ℝ) *
    (1 / r) ^ (d + 1)

/-- `|a + b| - |a| ≥ sgn(a) b + [a = 0] |b|`. -/
theorem sign_mul_add_le (a b : ℝ) :
    Real.sign a * b + (if a = 0 then |b| else 0) ≤ |a + b| - |a| := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [Real.sign_of_neg h, if_neg h.ne, abs_of_neg h]
    linarith [neg_abs_le (a + b)]
  · rw [Real.sign_zero, if_pos rfl, zero_mul, zero_add, zero_add, abs_zero, sub_zero]
  · rw [Real.sign_of_pos h, if_neg h.ne', abs_of_pos h]
    linarith [le_abs_self (a + b)]

theorem summable_sign_mul {r : ℝ} (hr : 1 < r) (p d : ℝ[X]) :
    Summable fun k : ℕ => Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) *
      (1 / r) ^ (k + 1) :=
  Summable.of_norm_bounded (summable_rowPhi hr d) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (1 / r) ^ (k + 1))]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rcases lt_trichotomy (p.eval ((k + 1 : ℕ) : ℝ)) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_neg, abs_one, one_mul]
    · rw [h, Real.sign_zero, abs_zero, zero_mul]
      exact abs_nonneg _
    · rw [Real.sign_of_pos h, abs_one, one_mul]

theorem summable_zero_mul {r : ℝ} (hr : 1 < r) (p d : ℝ[X]) :
    Summable fun k : ℕ =>
      (if p.eval ((k + 1 : ℕ) : ℝ) = 0 then |d.eval ((k + 1 : ℕ) : ℝ)| else 0) *
        (1 / r) ^ (k + 1) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (by split_ifs <;> positivity) (by positivity))
    (fun k => mul_le_mul_of_nonneg_right (by split_ifs; exacts [le_rfl, abs_nonneg _])
      (by positivity))
    (summable_rowPhi hr d)

/-- `Φ_r(q) - Φ_r(Z) ≥ ∑_{y ∈ Z \ S} (c_y G_y + |c_y| |e_y(y)| r^{-y})` with
`c_y = (q - r_Z)(y)/e_y(y)`, for every admissible `q` of `μ_r(S, |Z| + 1)`. -/
theorem rowPhi_sub_ge_sum {r : ℝ} (hr : 1 < r) {S Z : Finset ℕ} (hSZ : S ⊆ Z) (h0 : 0 ∉ Z)
    {q : ℝ[X]} (hq : q.degree < ↑(Z.card + 1)) (hq0 : q.eval 0 = 1)
    (hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0) :
    ∑ y ∈ Z \ S, ((q - confPolyP Z).eval (y : ℝ) / (eY Z y).eval (y : ℝ) * gY r Z y +
      |(q - confPolyP Z).eval (y : ℝ) / (eY Z y).eval (y : ℝ)| * |(eY Z y).eval (y : ℝ)| *
        (1 / r) ^ y) ≤ rowPhi r q - rowPhi r (confPolyP Z) := by
  set p := confPolyP Z
  obtain ⟨-, hp0, hpZ⟩ := confPolyP_admissible (L := Z.card + 1) h0 (by omega)
  have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  have hqn : q.natDegree ≤ Z.card := by
    rw [degree_eq_natDegree hqne] at hq
    exact Nat.lt_succ_iff.1 (by exact_mod_cast hq)
  set d := q - p
  have hdn : d.natDegree ≤ Z.card :=
    (natDegree_sub_le _ _).trans (max_le hqn (natDegree_confPolyP Z))
  have hd0 : d.eval 0 = 0 := by rw [eval_sub, hq0, hp0, sub_self]
  have hdS : ∀ s ∈ S, d.eval (s : ℝ) = 0 := fun s hs => by
    rw [eval_sub, hqS s hs, hpZ s (hSZ hs), sub_self]
  have hdec := eq_sum_eY h0 hdn hd0 hdS
  have hqpd : q = p + d := by rw [add_sub_cancel]
  -- pointwise
  have hpt : ∀ k : ℕ, Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) *
      (1 / r) ^ (k + 1) +
        (if p.eval ((k + 1 : ℕ) : ℝ) = 0 then |d.eval ((k + 1 : ℕ) : ℝ)| else 0) *
          (1 / r) ^ (k + 1) ≤
      |q.eval ((k + 1 : ℕ) : ℝ)| * (1 / r) ^ (k + 1) -
        |p.eval ((k + 1 : ℕ) : ℝ)| * (1 / r) ^ (k + 1) :=
    fun k => by
      rw [← add_mul, ← sub_mul, hqpd, eval_add]
      exact mul_le_mul_of_nonneg_right (sign_mul_add_le _ _) (by positivity)
  have hs1 := summable_sign_mul hr p d
  have hs2 := summable_zero_mul hr p d
  have hmain := Summable.tsum_le_tsum hpt (hs1.add hs2)
    ((summable_rowPhi hr q).sub (summable_rowPhi hr p))
  rw [hs1.tsum_add hs2, (summable_rowPhi hr q).tsum_sub (summable_rowPhi hr p)] at hmain
  -- the first sum is `∑_y c_y G_y`
  have hT1 : ∑' k : ℕ, Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) *
      (1 / r) ^ (k + 1) = ∑ y ∈ Z \ S, (d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)) * gY r Z y := by
    have e : ∀ k : ℕ, Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) *
        (1 / r) ^ (k + 1) = ∑ y ∈ Z \ S, (d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)) *
          (Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * (eY Z y).eval ((k + 1 : ℕ) : ℝ) *
            (1 / r) ^ (k + 1)) := fun k => by
      conv_lhs => rw [hdec, eval_finset_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by rw [eval_mul, eval_C]; ring
    rw [tsum_congr e, Summable.tsum_finsetSum fun y _ => (summable_sign_mul hr p _).mul_left _]
    exact Finset.sum_congr rfl fun y _ => by rw [tsum_mul_left, gY]
  -- the second sum is at least `∑_y |d(y)| r^{-y}`
  have hT2 : ∑ y ∈ Z \ S,
      |d.eval (y : ℝ) / (eY Z y).eval (y : ℝ)| * |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y ≤
      ∑' k : ℕ, (if p.eval ((k + 1 : ℕ) : ℝ) = 0 then |d.eval ((k + 1 : ℕ) : ℝ)| else 0) *
        (1 / r) ^ (k + 1) := by
    have hinj : Set.InjOn (fun y : ℕ => y - 1) ((Z \ S : Finset ℕ) : Set ℕ) :=
      fun a ha b hb h => by
      have ha0 : a ≠ 0 := fun h' => h0 (h' ▸ (Finset.mem_sdiff.1 (Finset.mem_coe.1 ha)).1)
      have hb0 : b ≠ 0 := fun h' => h0 (h' ▸ (Finset.mem_sdiff.1 (Finset.mem_coe.1 hb)).1)
      have : a - 1 = b - 1 := h
      omega
    refine le_trans (le_of_eq ?_) (hs2.sum_le_tsum ((Z \ S).image fun y => y - 1)
      fun k _ => mul_nonneg (by split_ifs <;> positivity) (by positivity))
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyZ := (Finset.mem_sdiff.1 hy).1
    have hy1 : y - 1 + 1 = y := Nat.sub_add_cancel (Nat.pos_of_ne_zero fun h => h0 (h ▸ hyZ))
    rw [hy1, if_pos (hpZ y hyZ), abs_div,
      div_mul_cancel₀ _ (abs_ne_zero.2 (eval_eY_self_ne h0 hyZ))]
  rw [Finset.sum_add_distrib, ← hT1]
  unfold rowPhi
  linarith

/-- Lemma 6.11 of `coefficient-mass-rows.tex`, sufficiency: if `|G_y| ≤ |e_y(y)| r^{-y}` for
every `y ∈ Z \ S`, then `Φ_r(Z) ≤ Φ_r(q)` for every admissible `q` of `μ_r(S, |Z| + 1)`. -/
theorem rowPhi_le_of_cert {r : ℝ} (hr : 1 < r) {S Z : Finset ℕ} (hSZ : S ⊆ Z) (h0 : 0 ∉ Z)
    (hcert : ∀ y ∈ Z \ S, |gY r Z y| ≤ |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y)
    {q : ℝ[X]} (hq : q.degree < ↑(Z.card + 1)) (hq0 : q.eval 0 = 1)
    (hqS : ∀ s ∈ S, q.eval (s : ℝ) = 0) : rowPhi r (confPolyP Z) ≤ rowPhi r q := by
  refine sub_nonneg.1 (le_trans (Finset.sum_nonneg fun y hy => ?_)
    (rowPhi_sub_ge_sum hr hSZ h0 hq hq0 hqS))
  set c := (q - confPolyP Z).eval (y : ℝ) / (eY Z y).eval (y : ℝ)
  have h1 := mul_le_mul_of_nonneg_left (hcert y hy) (abs_nonneg c)
  have h2 := neg_abs_le (c * gY r Z y)
  rw [abs_mul] at h2
  nlinarith

end CoefficientMass
