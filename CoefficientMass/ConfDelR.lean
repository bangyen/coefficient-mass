/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.GeomSum
import CoefficientMass.RowValue

/-!
# Deleting the Largest Zero at a Root `r > 1`

This module proves the inequality of Lemma 2.3 of `coefficient-mass-rows.tex`,
`Φ_r(Z) ≤ max(1, a) Φ_r(Z \ {max Z})` with `a = 1/(r - 1)`, directly, without the limit
of merging nodes.  With `x = 1/r`, `z = max Z`, `Z' = Z \ {z}` and `m = max(1, a)`,
`m Φ_r(Z') - Φ_r(Z)` is the sum of `|r_{Z'}(s)| x^s (m - |1 - s/z|)`.  The terms with
`s < z` are nonnegative.  Beyond `z`, `|r_{Z'}(z + t)| = ∏_{c ∈ A} (t + c) / ∏_{w ∈ Z'} w`
with `A = z - Z'`, so these terms sum to a positive multiple of
`-S[(t - m z) ∏_{c ∈ A} (t + c)] ≥ 0`, as `(1 - x) m z ≥ (1 - x) a (|Z'| + 1) = x (|Z'| + 1)`.

## Theorems

* `rowPhi_conf`.
* `summable_conf`.
* `abs_confPoly_add`.
* `rowPhi_erase_max`.
-/

open Polynomial

namespace CoefficientMass

theorem rowPhi_conf (r : ℝ) (Z : Finset ℕ) :
    rowPhi r (confPolyP Z) = ∑' d : ℕ, |confPoly Z (d + 1)| * (1 / r) ^ (d + 1) :=
  tsum_congr fun d => by rw [confPoly_eq_eval]

theorem summable_conf {r : ℝ} (hr : 1 < r) (Z : Finset ℕ) :
    Summable fun d : ℕ => |confPoly Z (d + 1)| * (1 / r) ^ (d + 1) :=
  (summable_rowPhi hr (confPolyP Z)).congr fun d => by rw [confPoly_eq_eval]

/-- Beyond a bound `z` on `W ⊂ ℕ_{>0}`, `|r_W(z + t)| = ∏_{w ∈ W} (t + (z - w)) / ∏ W`. -/
theorem abs_confPoly_add {W : Finset ℕ} {z : ℕ} (hpos : ∀ w ∈ W, 0 < w) (hlt : ∀ w ∈ W, w < z)
    (t : ℕ) : |confPoly W (t + z)| =
      (risingP (W.image fun w => z - w)).eval (t : ℝ) / ∏ w ∈ W, (w : ℝ) := by
  have hinj : Set.InjOn (fun w => z - w) (W : Set ℕ) := fun v hv w hw h => by
    have h' : z - v = z - w := h
    have := hlt v hv
    have := hlt w hw
    omega
  have hfac : ∀ w ∈ W, |1 - ((t + z : ℕ) : ℝ) / w| = ((t : ℝ) + ((z - w : ℕ) : ℝ)) / w :=
    fun w hw => by
      have hw0 : (0 : ℝ) < w := by exact_mod_cast hpos w hw
      have hwz : (w : ℝ) < z := by exact_mod_cast hlt w hw
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      rw [Nat.cast_sub (hlt w hw).le, Nat.cast_add, abs_of_nonpos (by
        rw [sub_nonpos, le_div_iff₀ hw0]
        linarith)]
      rw [neg_sub, div_sub_one hw0.ne']
      ring
  rw [confPoly, Finset.abs_prod, Finset.prod_congr rfl hfac, Finset.prod_div_distrib, risingP,
    eval_prod, Finset.prod_image hinj]
  simp only [eval_add, eval_X, eval_C]

/-- `Φ_r(Z) ≤ max(1, a) Φ_r(Z \ {max Z})`, `a = 1/(r - 1)`. -/
theorem rowPhi_erase_max {r : ℝ} (hr : 1 < r) {Z : Finset ℕ} (hne : Z.Nonempty) (h0 : 0 ∉ Z) :
    rowPhi r (confPolyP Z) ≤
      max 1 (1 / (r - 1)) * rowPhi r (confPolyP (Z.erase (Z.max' hne))) := by
  set x : ℝ := 1 / r with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; exact hr
  set m := max 1 (1 / (r - 1))
  have hm1 : 1 ≤ m := le_max_left _ _
  have hma : 1 / (r - 1) ≤ m := le_max_right _ _
  have hxa : (1 - x) * (1 / (r - 1)) = x := by
    have : r - 1 ≠ 0 := by linarith
    rw [hx]
    field_simp
  set z := Z.max' hne
  set Z' := Z.erase z with hZ'
  have hz : z ∈ Z := Z.max'_mem hne
  have hz1 : 1 ≤ z := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hz)
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlt : ∀ w ∈ Z', w < z := fun w hw =>
    lt_of_le_of_ne (Z.le_max' w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw)
  have hpos : ∀ w ∈ Z', 0 < w := fun w hw =>
    Nat.pos_of_ne_zero fun h => h0 (h ▸ Finset.mem_of_mem_erase hw)
  have hsplit : ∀ s : ℕ, confPoly Z s = (1 - (s : ℝ) / z) * confPoly Z' s := fun s => by
    rw [confPoly, confPoly, ← Finset.mul_prod_erase Z _ hz]
  set g : ℕ → ℝ := fun d => m * (|confPoly Z' (d + 1)| * x ^ (d + 1)) -
    |confPoly Z (d + 1)| * x ^ (d + 1) with hg
  have hgs : Summable g := ((summable_conf hr Z').mul_left m).sub (summable_conf hr Z)
  have hdiff : m * rowPhi r (confPolyP Z') - rowPhi r (confPolyP Z) = ∑' d, g d := by
    rw [rowPhi_conf, rowPhi_conf, ← tsum_mul_left]
    exact (((summable_conf hr Z').mul_left m).tsum_sub (summable_conf hr Z)).symm
  have hlow : ∀ d, d + 1 < z → 0 ≤ g d := fun d hd => by
    have hq : ((d + 1 : ℕ) : ℝ) / z ≤ 1 := by rw [div_le_one hzpos]; exact_mod_cast hd.le
    have hq0 : 0 ≤ ((d + 1 : ℕ) : ℝ) / z := by positivity
    have hv : 0 ≤ |confPoly Z' (d + 1)| * x ^ (d + 1) := by positivity
    simp only [hg]
    rw [hsplit, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ((d + 1 : ℕ) : ℝ) / z)]
    nlinarith [mul_nonneg hq0 hv, mul_nonneg (sub_nonneg.2 hm1) hv]
  -- the terms beyond `z`
  set A := Z'.image fun w => z - w with hAdef
  set R := risingP A with hR
  have hinj : Set.InjOn (fun w => z - w) (Z' : Set ℕ) := fun v hv w hw h => by
    have h' : z - v = z - w := h
    have := hlt v hv
    have := hlt w hw
    omega
  have hA0 : 0 ∉ A := fun h => by
    obtain ⟨w, hw, hw0⟩ := Finset.mem_image.1 h
    have := hlt w hw
    omega
  have hAcard : A.card = Z'.card := Finset.card_image_of_injOn hinj
  have hP : 0 < ∏ w ∈ Z', (w : ℝ) := Finset.prod_pos fun w hw => by exact_mod_cast hpos w hw
  have hv : ∀ t : ℕ, |confPoly Z' (t + z)| = R.eval (t : ℝ) / ∏ w ∈ Z', (w : ℝ) :=
    abs_confPoly_add hpos hlt
  have htail : ∀ t : ℕ, g (t + (z - 1)) = -(x ^ z / (z * ∏ w ∈ Z', (w : ℝ))) *
      (((X - C (m * z)) * R).eval (t : ℝ) * x ^ t) := fun t => by
    have hs : t + (z - 1) + 1 = t + z := by omega
    have habs : |1 - ((t + z : ℕ) : ℝ) / z| = t / z := by
      rw [Nat.cast_add, show (1 : ℝ) - (t + z) / z = -(t / z) by
        rw [add_div, div_self hzpos.ne']; ring, abs_neg, abs_of_nonneg (by positivity)]
    simp only [hg]
    rw [hs, hsplit, abs_mul, habs, hv, eval_mul, eval_sub, eval_X, eval_C, pow_add]
    field_simp
    ring
  have hT : ∑' t, g (t + (z - 1)) = -(x ^ z / (z * ∏ w ∈ Z', (w : ℝ))) *
      geomSum x ((X - C (m * z)) * R) := by
    rw [tsum_congr htail, tsum_mul_left, geomSum]
  have hK : 0 < x ^ z / (z * ∏ w ∈ Z', (w : ℝ)) := by positivity
  have hfin : 0 ≤ ∑ d ∈ Finset.range (z - 1), g d := Finset.sum_nonneg fun d hd => by
    have := Finset.mem_range.1 hd
    exact hlow d (by omega)
  have hall := hgs.sum_add_tsum_nat_add (z - 1)
  -- the sign of the sum beyond `z`
  have hk : Z'.card + 1 ≤ z := by
    have := Finset.card_le_card fun w (hw : w ∈ Z') => Finset.mem_Ioo.2 ⟨hpos w hw, hlt w hw⟩
    rw [Nat.card_Ioo] at this
    omega
  have hkz : ((Z'.card : ℝ) + 1) ≤ z := by exact_mod_cast hk
  have hcond : ((Z'.card : ℝ) + 1) * x ≤ (1 - x) * (m * z) := by
    have ha0 : 0 ≤ 1 / (r - 1) := by
      have : 0 < r - 1 := by linarith
      positivity
    calc ((Z'.card : ℝ) + 1) * x = ((Z'.card : ℝ) + 1) * ((1 - x) * (1 / (r - 1))) := by
          rw [hxa]
      _ ≤ z * ((1 - x) * m) :=
          mul_le_mul hkz (mul_le_mul_of_nonneg_left hma (by linarith))
            (mul_nonneg (by linarith) ha0) hzpos.le
      _ = (1 - x) * (m * z) := by ring
  have key := geomSum_sub_mul_risingP_nonpos hx0.le hx1 _ _ A hAcard rfl hA0 (m * z) hcond
  have := mul_nonneg_of_nonpos_of_nonpos (by linarith : -(x ^ z /
    (z * ∏ w ∈ Z', (w : ℝ))) ≤ 0) key
  linarith

end CoefficientMass
