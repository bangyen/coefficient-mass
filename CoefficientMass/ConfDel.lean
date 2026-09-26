/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.GeomSum

/-!
# Deleting the Largest Zero

This module proves Lemma 4.6 of `coefficient-mass.tex` directly, without the
limit of merging nodes.  With `z = max Z` and `Z' = Z \ {z}`,
`r_Z(s) = (1 - s/z) r_{Z'}(s)`, so `Φ(Z') - Φ(Z)` is the sum of
`|r_{Z'}(s)| 2^{-s} (1 - |1 - s/z|)`.  The terms with `s < z` are
nonnegative.  For `s = z + t` every factor of `r_{Z'}` is negative, and
`|r_{Z'}(z + t)| = ∏_{a ∈ A} (t + a) / ∏_{x ∈ Z'} x` with `A = z - Z'`, a set
of `|Z'|` positive integers; the terms beyond `z` sum to a positive multiple
of `-S[(t - z) ∏_{a ∈ A} (t + a)] ≥ 0`, strictly when `z > |Z|`.  Deleting
the largest element repeatedly ends at `Φ(∅) = 1`.

## Definitions

* `DeleteLargest`.

## Theorems

* `confTail_empty`.
* `confTail_erase_max`.
* `confTail_le_one`.
* `deleteLargest`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 4.6 (deleting the largest zero): for nonempty `Z ⊂ ℕ_{>0}`,
`Φ(Z) ≤ Φ(Z \ {max Z})`, strictly unless `Z = {1, …, |Z|}`, and `Φ(Z) ≤ 1`. -/
def DeleteLargest : Prop :=
  ∀ (Z : Finset ℕ) (hne : Z.Nonempty), 0 ∉ Z →
    confTail Z ≤ confTail (Z.erase (Z.max' hne)) ∧
      (Z.card < Z.max' hne → confTail Z < confTail (Z.erase (Z.max' hne))) ∧ confTail Z ≤ 1

theorem confTail_empty : confTail ∅ = 1 := by
  have e : ∀ d : ℕ, |confPoly ∅ (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) = 1 / 2 * (1 / 2) ^ d :=
    fun d => by rw [confPoly, Finset.prod_empty, abs_one, one_mul, pow_succ, mul_comm]
  rw [confTail, tsum_congr e, tsum_mul_left, tsum_geometric_two]
  norm_num

/-- `Φ(Z) ≤ Φ(Z \ {max Z})`, strictly when `max Z > |Z|`. -/
theorem confTail_erase_max {Z : Finset ℕ} (hne : Z.Nonempty) (h0 : 0 ∉ Z) :
    confTail Z ≤ confTail (Z.erase (Z.max' hne)) ∧
      (Z.card < Z.max' hne → confTail Z < confTail (Z.erase (Z.max' hne))) := by
  set z := Z.max' hne
  set Z' := Z.erase z with hZ'
  have hz : z ∈ Z := Z.max'_mem hne
  have hz1 : 1 ≤ z := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hz)
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlt : ∀ x ∈ Z', x < z := fun x hx =>
    lt_of_le_of_ne (Z.le_max' x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hpos : ∀ x ∈ Z', 0 < x := fun x hx =>
    Nat.pos_of_ne_zero fun h => h0 (h ▸ Finset.mem_of_mem_erase hx)
  have hsplit : ∀ s : ℕ, confPoly Z s = (1 - (s : ℝ) / z) * confPoly Z' s := fun s => by
    rw [confPoly, confPoly, ← Finset.mul_prod_erase Z _ hz]
  set g : ℕ → ℝ := fun d => |confPoly Z' (d + 1)| * (1 / 2) ^ (d + 1) -
    |confPoly Z (d + 1)| * (1 / 2) ^ (d + 1) with hg
  have hgs : Summable g := (summable_confTail Z').sub (summable_confTail Z)
  have hdiff : confTail Z' - confTail Z = ∑' d, g d :=
    ((summable_confTail Z').tsum_sub (summable_confTail Z)).symm
  have hlow : ∀ d, d + 1 < z → 0 ≤ g d := fun d hd => by
    have hq : ((d + 1 : ℕ) : ℝ) / z ≤ 1 := by rw [div_le_one hzpos]; exact_mod_cast hd.le
    have hq0 : 0 ≤ ((d + 1 : ℕ) : ℝ) / z := by positivity
    have hv : 0 ≤ |confPoly Z' (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) := by positivity
    simp only [hg]
    rw [hsplit, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ((d + 1 : ℕ) : ℝ) / z)]
    nlinarith [mul_nonneg hq0 hv]
  -- the terms beyond `z`
  set A := Z'.image fun x => z - x with hAdef
  set R := risingP A with hR
  have hinj : Set.InjOn (fun x => z - x) (Z' : Set ℕ) := fun x hx y hy h => by
    have h' : z - x = z - y := h
    have := hlt x hx
    have := hlt y hy
    omega
  have hA0 : 0 ∉ A := fun h => by
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 h
    have := hlt x hx
    omega
  have hAcard : A.card = Z'.card := Finset.card_image_of_injOn hinj
  have hP : 0 < ∏ x ∈ Z', (x : ℝ) := Finset.prod_pos fun x hx => by exact_mod_cast hpos x hx
  have hfac : ∀ t : ℕ, ∀ x ∈ Z', |1 - ((t + z : ℕ) : ℝ) / x| = ((t : ℝ) + ((z - x : ℕ) : ℝ)) / x :=
    fun t x hx => by
      have hx0 : (0 : ℝ) < x := by exact_mod_cast hpos x hx
      have hxz : (x : ℝ) < z := by exact_mod_cast hlt x hx
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      rw [Nat.cast_sub (hlt x hx).le, Nat.cast_add, abs_of_nonpos (by
        rw [sub_nonpos, le_div_iff₀ hx0]
        linarith)]
      rw [neg_sub, div_sub_one hx0.ne']
      ring
  have hv : ∀ t : ℕ, |confPoly Z' (t + z)| = R.eval (t : ℝ) / ∏ x ∈ Z', (x : ℝ) := fun t => by
    rw [confPoly, Finset.abs_prod, Finset.prod_congr rfl (hfac t), Finset.prod_div_distrib, hR,
      risingP, eval_prod, hAdef, Finset.prod_image hinj]
    simp only [eval_add, eval_X, eval_C]
  have htail : ∀ t : ℕ, g (t + (z - 1)) = -((1 / 2) ^ z / (z * ∏ x ∈ Z', (x : ℝ))) *
      (((X - C (z : ℝ)) * R).eval (t : ℝ) * (1 / 2) ^ t) := fun t => by
    have hs : t + (z - 1) + 1 = t + z := by omega
    have habs : |1 - ((t + z : ℕ) : ℝ) / z| = t / z := by
      rw [Nat.cast_add, show (1 : ℝ) - (t + z) / z = -(t / z) by
        rw [add_div, div_self hzpos.ne']; ring, abs_neg, abs_of_nonneg (by positivity)]
    simp only [hg]
    rw [hs, hsplit, abs_mul, habs, hv, eval_mul, eval_sub, eval_X, eval_C, pow_add]
    field_simp
    ring
  have hT : ∑' t, g (t + (z - 1)) = -((1 / 2) ^ z / (z * ∏ x ∈ Z', (x : ℝ))) *
      geomSum (1 / 2) ((X - C (z : ℝ)) * R) := by
    rw [tsum_congr htail, tsum_mul_left, geomSum]
  have hK : 0 < (1 / 2 : ℝ) ^ z / (z * ∏ x ∈ Z', (x : ℝ)) := by positivity
  have hfin : 0 ≤ ∑ d ∈ Finset.range (z - 1), g d := Finset.sum_nonneg fun d hd => by
    have := Finset.mem_range.1 hd
    exact hlow d (by omega)
  have hall := hgs.sum_add_tsum_nat_add (z - 1)
  -- the sign of the sum beyond `z`
  have hk : Z'.card + 1 ≤ z := by
    have := Finset.card_le_card fun x (hx : x ∈ Z') => Finset.mem_Ioo.2 ⟨hpos x hx, hlt x hx⟩
    rw [Nat.card_Ioo] at this
    omega
  have hZc : Z.card = Z'.card + 1 := (Finset.card_erase_add_one hz).symm
  have key := geomSum_sub_mul_risingP_nonpos (x := 1 / 2) (by norm_num) (by norm_num) _ _ A
    hAcard rfl hA0 ((Z'.card : ℝ) + 1) (le_of_eq (by ring))
  have hRpos := geomSum_pos (x := 1 / 2) (by norm_num) (by norm_num) (p := R)
    (fun t => (eval_risingP_pos hA0 (Nat.cast_nonneg t)).le)
    (eval_risingP_pos hA0 le_rfl)
  have hGz : geomSum (1 / 2) ((X - C (z : ℝ)) * R) =
      geomSum (1 / 2) ((X - C ((Z'.card : ℝ) + 1)) * R) -
        ((z : ℝ) - (Z'.card + 1)) * geomSum (1 / 2) R := by
    rw [← geomSum_C_mul, ← geomSum_sub (by norm_num) (by norm_num), map_sub]
    congr 1
    ring
  have hkz : ((Z'.card : ℝ) + 1) ≤ z := by exact_mod_cast hk
  constructor
  · have : geomSum (1 / 2) ((X - C (z : ℝ)) * R) ≤ 0 := by rw [hGz]; nlinarith
    have := mul_nonneg_of_nonpos_of_nonpos (by linarith : -((1 / 2 : ℝ) ^ z /
      (z * ∏ x ∈ Z', (x : ℝ))) ≤ 0) this
    linarith
  · intro hc
    have hkz' : ((Z'.card : ℝ) + 1) < z := by exact_mod_cast (show Z'.card + 1 < z by omega)
    have : geomSum (1 / 2) ((X - C (z : ℝ)) * R) < 0 := by rw [hGz]; nlinarith
    have := mul_pos_of_neg_of_neg (by linarith : -((1 / 2 : ℝ) ^ z /
      (z * ∏ x ∈ Z', (x : ℝ))) < 0) this
    linarith

/-- `Φ(Z) ≤ 1`: delete the largest element until `Z = ∅`. -/
theorem confTail_le_one : ∀ (n : ℕ) (Z : Finset ℕ), Z.card = n → 0 ∉ Z → confTail Z ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro Z hZ _
    rw [Finset.card_eq_zero.1 hZ, confTail_empty]
  | succ n ih =>
    intro Z hZ h0
    have hne : Z.Nonempty := Finset.card_pos.1 (by omega)
    exact (confTail_erase_max hne h0).1.trans (ih _ (by
      rw [Finset.card_erase_of_mem (Z.max'_mem hne), hZ, Nat.add_sub_cancel])
      fun h => h0 (Finset.mem_of_mem_erase h))

/-- Lemma 4.6 (deleting the largest zero). -/
theorem deleteLargest : DeleteLargest := fun Z hne h0 =>
  ⟨(confTail_erase_max hne h0).1, (confTail_erase_max hne h0).2, confTail_le_one _ Z rfl h0⟩

end CoefficientMass
