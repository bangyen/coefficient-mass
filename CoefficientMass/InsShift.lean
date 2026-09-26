/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.InsPoly

/-!
# Shifting Past an Insertion

This module proves two more facts behind Lemma 5.2 of `coefficient-mass-rows.tex`, with
`κ = 1/(c B(-1))`, `B(-1) = ∏_{w ∈ W, w > c} (1 + 1/w)`.  Above the gap,
`|r_{ins(W, c)}(u + 1)| ≤ κ u |r_W(u)|` for `u ≥ c`: the factors of `B` shift by one at the
cost `w/(w + 1)`, and `|A(u + 1)|(u + 1 - c) ≤ u |A(u)|` since the ratio
`∏_{z < c} (u + 1 - z)/(u - z)` is at most its telescoping value over all of `[1, c - 1]`.
And the leading coefficient of `r_{ins(W, c)}` is `-κ` times that of `r_W`.

## Definitions

* `kappa`.

## Theorems

* `prod_ins`.
* `prod_telescope`.
* `abs_prefix_shift`.
* `abs_ins_shift`.
* `coeff_linear_mul`.
* `coeff_confPolyP_card`.
* `coeff_ins_card`.
-/

open Polynomial

namespace CoefficientMass

/-- `κ = 1/(c ∏_{w ∈ W, w ≥ c} (1 + 1/w))`. -/
noncomputable def kappa (W : Finset ℕ) (c : ℕ) : ℝ :=
  1 / (c * ∏ w ∈ W.filter (c ≤ ·), (1 + 1 / (w : ℝ)))

/-- A product over `ins(W, c)` splits at `c`. -/
theorem prod_ins {W : Finset ℕ} {c : ℕ} (hc : c ∉ W) (f : ℕ → ℝ) :
    ∏ z ∈ ins W c, f z = (∏ w ∈ W.filter (· < c), f w) * f c *
      ∏ w ∈ W.filter (c ≤ ·), f (w + 1) := by
  classical
  have hdisj : Disjoint (W.filter (· < c)) (insert c ((W.filter (c ≤ ·)).image (· + 1))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := (Finset.mem_filter.1 hx).2
    rcases Finset.mem_insert.1 hx' with rfl | hx'
    · exact lt_irrefl _ this
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx'
      have := (Finset.mem_filter.1 hw).2
      omega
  have hnot : c ∉ (W.filter (c ≤ ·)).image (· + 1) := fun hh => by
    obtain ⟨w, hw, hwc⟩ := Finset.mem_image.1 hh
    have := (Finset.mem_filter.1 hw).2
    omega
  rw [ins, Finset.prod_union hdisj, Finset.prod_insert hnot,
    Finset.prod_image fun a _ b _ h => by simpa only [add_left_inj] using h, mul_assoc]

/-- `∏_{z = 1}^j (u + 1 - z)/(u - z) = u/(u - j)` for `j < u`. -/
theorem prod_telescope {u : ℝ} :
    ∀ j : ℕ, (j : ℝ) < u → ∏ z ∈ Finset.Icc 1 j, (u + 1 - z) / (u - z) = u / (u - j) := by
  intro j
  induction j with
  | zero =>
    intro hu
    rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, Nat.cast_zero, sub_zero,
      div_self (by linarith)]
  | succ j ih =>
    intro hu
    push_cast at hu
    rw [Finset.prod_Icc_succ_top (by omega), ih (by linarith)]
    push_cast
    have h1 : u - j ≠ 0 := by linarith
    have h2 : u - (j + 1) ≠ 0 := by linarith
    field_simp
    ring

/-- `|A(u + 1)| (u + 1 - c) ≤ u |A(u)|` for `A = ∏_{z ∈ Z} (1 - s/z)`, `Z ⊆ [1, c - 1]`,
`u ≥ c`. -/
theorem abs_prefix_shift {Z : Finset ℕ} {c : ℕ} (hc1 : 1 ≤ c) (hZ : ∀ z ∈ Z, 1 ≤ z ∧ z < c)
    {u : ℕ} (hu : c ≤ u) :
    |∏ z ∈ Z, (1 - ((u + 1 : ℕ) : ℝ) / z)| * (((u + 1 : ℕ) : ℝ) - c) ≤
      u * |∏ z ∈ Z, (1 - (u : ℝ) / z)| := by
  have hu' : (c : ℝ) ≤ u := by exact_mod_cast hu
  have hpos : ∀ z ∈ Z, (0 : ℝ) < u - z ∧ (0 : ℝ) < z := fun z hz => by
    obtain ⟨h1, h2⟩ := hZ z hz
    have : (z : ℝ) < c := by exact_mod_cast h2
    exact ⟨by linarith, by exact_mod_cast h1⟩
  have hfac : ∀ z ∈ Z, |1 - ((u + 1 : ℕ) : ℝ) / z| =
      |1 - (u : ℝ) / z| * (((u : ℝ) + 1 - z) / (u - z)) := fun z hz => by
    obtain ⟨h1, h2⟩ := hpos z hz
    push_cast
    rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ h2]; linarith),
      abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ h2]; linarith)]
    field_simp
    ring
  rw [Finset.abs_prod, Finset.abs_prod, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have hratio : ∏ z ∈ Z, (((u : ℝ) + 1 - z) / (u - z)) ≤ u / (u + 1 - c) := by
    have hsub : Z ⊆ Finset.Icc 1 (c - 1) := fun z hz => by
      obtain ⟨h1, h2⟩ := hZ z hz
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    have hgeq : ∀ z ∈ Finset.Icc 1 (c - 1), 1 ≤ ((u : ℝ) + 1 - z) / (u - z) := fun z hz => by
      have := (Finset.mem_Icc.1 hz).2
      have hz' : (z : ℝ) < u := by exact_mod_cast (show z < u by omega)
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hrest : 1 ≤ ∏ z ∈ Finset.Icc 1 (c - 1) \ Z, (((u : ℝ) + 1 - z) / (u - z)) := by
      have := Finset.prod_le_prod (s := Finset.Icc 1 (c - 1) \ Z) (f := fun _ => (1 : ℝ))
        (fun _ _ => zero_le_one) fun z hz => hgeq z (Finset.sdiff_subset hz)
      rwa [Finset.prod_const_one] at this
    have hZ0 : 0 ≤ ∏ z ∈ Z, (((u : ℝ) + 1 - z) / (u - z)) := Finset.prod_nonneg fun z hz =>
      (zero_le_one.trans (hgeq z (hsub hz)))
    refine (le_mul_of_one_le_left hZ0 hrest).trans_eq ?_
    rw [Finset.prod_sdiff hsub]
    have := prod_telescope (u := (u : ℝ)) (c - 1) (by
      rw [Nat.cast_sub hc1]; push_cast; linarith)
    rw [this, Nat.cast_sub hc1]
    push_cast
    ring_nf
  have hA := Finset.prod_nonneg fun z (_ : z ∈ Z) => abs_nonneg (1 - (u : ℝ) / z)
  have hcpos : (0 : ℝ) < u + 1 - c := by linarith
  push_cast
  have hc1' := hcpos.ne'
  calc (∏ z ∈ Z, |1 - (u : ℝ) / z|) * (∏ z ∈ Z, (((u : ℝ) + 1 - z) / (u - z))) * (u + 1 - c)
      ≤ (∏ z ∈ Z, |1 - (u : ℝ) / z|) * (u / (u + 1 - c)) * (u + 1 - c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hA) hcpos.le
    _ = u * ∏ z ∈ Z, |1 - (u : ℝ) / z| := by
        rw [mul_assoc, div_mul_cancel₀ _ hc1', mul_comm]

/-- Above the gap: `|r_{ins(W, c)}(u + 1)| ≤ κ u |r_W(u)|` for `u ≥ c ≥ 1`. -/
theorem abs_ins_shift {W : Finset ℕ} {c : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hc1 : 1 ≤ c) {u : ℕ}
    (hu : c ≤ u) :
    |(confPolyP (ins W c)).eval ((u + 1 : ℕ) : ℝ)| ≤
      kappa W c * u * |(confPolyP W).eval (u : ℝ)| := by
  classical
  set U := W.filter (c ≤ ·) with hUdef
  have hU : ∀ w ∈ U, (0 : ℝ) < w := fun w hw => by
    exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ (Finset.mem_filter.1 hw).1)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
  have hu' : (c : ℝ) ≤ u := by exact_mod_cast hu
  have hBm : 0 < ∏ w ∈ U, (1 + 1 / (w : ℝ)) := Finset.prod_pos fun w hw => by
    have := hU w hw
    positivity
  -- the factors above `c` shift by one
  have hshift : ∏ w ∈ U, (1 - ((u + 1 : ℕ) : ℝ) / ((w : ℝ) + 1)) =
      (∏ w ∈ U, (1 - (u : ℝ) / w)) / ∏ w ∈ U, (1 + 1 / (w : ℝ)) := by
    rw [eq_div_iff hBm.ne', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w hw => ?_
    have := hU w hw
    push_cast
    field_simp
    ring
  have hA := abs_prefix_shift (Z := W.filter (· < c)) (c := c) hc1 (fun z hz => by
    obtain ⟨hzW, hzc⟩ := Finset.mem_filter.1 hz
    exact ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ hzW), hzc⟩) hu
  rw [eval_confPolyP_ins hc, eval_confPolyP_split W c, hshift, abs_mul, abs_mul, abs_mul,
    abs_div, abs_of_pos hBm, kappa, ← hUdef]
  have hcs : |1 - ((u + 1 : ℕ) : ℝ) / c| = (((u + 1 : ℕ) : ℝ) - c) / c := by
    push_cast
    rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ hc0]; linarith), neg_sub,
      div_sub_one hc0.ne']
  rw [hcs]
  have hB := abs_nonneg (∏ w ∈ U, (1 - (u : ℝ) / w))
  have hA0 := abs_nonneg (∏ w ∈ W.filter (· < c), (1 - (u : ℝ) / w))
  have hkey : |∏ w ∈ W.filter (· < c), (1 - ((u + 1 : ℕ) : ℝ) / w)| *
      ((((u + 1 : ℕ) : ℝ) - c) / c) ≤ u * |∏ w ∈ W.filter (· < c), (1 - (u : ℝ) / w)| / c := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hc0]
    exact hA
  calc |∏ w ∈ W.filter (· < c), (1 - ((u + 1 : ℕ) : ℝ) / w)| * ((((u + 1 : ℕ) : ℝ) - c) / c) *
        (|∏ w ∈ U, (1 - (u : ℝ) / w)| / ∏ w ∈ U, (1 + 1 / (w : ℝ)))
      ≤ u * |∏ w ∈ W.filter (· < c), (1 - (u : ℝ) / w)| / c *
          (|∏ w ∈ U, (1 - (u : ℝ) / w)| / ∏ w ∈ U, (1 + 1 / (w : ℝ))) :=
        mul_le_mul_of_nonneg_right hkey (div_nonneg hB hBm.le)
    _ = _ := by
        field_simp

/-- `coeff ((a x + 1) p) (n + 1) = a coeff p n + coeff p (n + 1)`. -/
theorem coeff_linear_mul (a : ℝ) (p : ℝ[X]) (n : ℕ) :
    ((C a * X + C 1) * p).coeff (n + 1) = a * p.coeff n + p.coeff (n + 1) := by
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, C_1, one_mul]

/-- The coefficient of `r_Z` of degree `|Z|` is `∏_{z ∈ Z} (-1/z)`. -/
theorem coeff_confPolyP_card (Z : Finset ℕ) :
    (confPolyP Z).coeff Z.card = ∏ z ∈ Z, (-(1 / (z : ℝ))) := by
  classical
  induction Z using Finset.induction_on with
  | empty => rw [confPolyP, Finset.prod_empty, Finset.prod_empty, Finset.card_empty, coeff_one_zero]
  | insert a Z ha ih =>
    rw [confPolyP, Finset.prod_insert ha, ← confPolyP, Finset.card_insert_of_notMem ha,
      coeff_linear_mul, ih, coeff_eq_zero_of_natDegree_lt ((natDegree_confPolyP Z).trans_lt
        (Nat.lt_succ_self _)), add_zero, Finset.prod_insert ha]

/-- The leading coefficients: `coeff_{|W| + 1}(r_{ins(W, c)}) = -κ coeff_{|W|}(r_W)`. -/
theorem coeff_ins_card {W : Finset ℕ} {c : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hc1 : 1 ≤ c) :
    (confPolyP (ins W c)).coeff (W.card + 1) = -(kappa W c * (confPolyP W).coeff W.card) := by
  classical
  have hcard : (ins W c).card = W.card + 1 := card_ins hc
  rw [← hcard, coeff_confPolyP_card, coeff_confPolyP_card, prod_ins hc,
    ← Finset.prod_filter_mul_prod_filter_not W (· < c), kappa]
  have hfe : W.filter (fun x => ¬ x < c) = W.filter (c ≤ ·) :=
    Finset.filter_congr fun x _ => not_lt
  rw [hfe]
  set U := W.filter (c ≤ ·)
  have hU : ∀ w ∈ U, (0 : ℝ) < w := fun w hw => by
    exact_mod_cast Nat.pos_of_ne_zero fun h => h0 (h ▸ (Finset.mem_filter.1 hw).1)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
  have hBm : 0 < ∏ w ∈ U, (1 + 1 / (w : ℝ)) := Finset.prod_pos fun w hw => by
    have := hU w hw
    positivity
  have hshift : ∏ w ∈ U, (-(1 / (((w + 1 : ℕ) : ℝ)))) =
      (∏ w ∈ U, (-(1 / (w : ℝ)))) / ∏ w ∈ U, (1 + 1 / (w : ℝ)) := by
    rw [eq_div_iff hBm.ne', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w hw => ?_
    have := hU w hw
    push_cast
    field_simp
  rw [hshift]
  field_simp

end CoefficientMass
