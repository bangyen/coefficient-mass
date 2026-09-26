/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Insert
import CoefficientMass.RowFarFactor

/-!
# The Polynomial of an Insertion

This module prepares Lemma 5.2 of `coefficient-mass-rows.tex`.  For `c ∉ W` write
`A(s) = ∏_{w < c} (1 - s/w)`, `B(s) = ∏_{w > c} (1 - s/w)` over `w ∈ W`, so `r_W = A B`, and
`r_{ins(W, c)}(s) = A(s) (1 - s/c) ∏_{w > c} (1 - s/(w + 1))`.  Below `c` the insertion has
the sign of `r_W` and is smaller in absolute value: `1 - s/(w + 1) = (1 - s/w) g(w)` with
`g(w) = 1 + s/((w - s)(w + 1))` decreasing, and the product of `g` over `m` integers above `c`
is at most its value on `c + 1, …, c + m`, which telescopes.  Above `c` the two have opposite
signs, since `(1 - s/w)(1 - s/(w + 1)) ≥ 0` at integers.

## Theorems

* `eval_confPolyP_split`.
* `eval_confPolyP_ins`.
* `prod_g_le`.
* `abs_ins_le_below`.
* `consecutive_factors_nonneg`.
* `ins_sign_below`.
* `ins_sign_above`.
-/

open Polynomial

namespace CoefficientMass

/-- `r_W = A B` with `A` over `W ∩ [1, c - 1]` and `B` over `W ∩ [c, ∞)`. -/
theorem eval_confPolyP_split (W : Finset ℕ) (c : ℕ) (y : ℝ) :
    (confPolyP W).eval y =
      (∏ w ∈ W.filter (· < c), (1 - y / w)) * ∏ w ∈ W.filter (c ≤ ·), (1 - y / w) := by
  classical
  rw [eval_confPolyP, ← Finset.prod_filter_mul_prod_filter_not W (· < c)]
  congr 1
  exact Finset.prod_congr (Finset.filter_congr fun x _ => not_lt) fun _ _ => rfl

/-- `r_{ins(W, c)}(y) = A(y) (1 - y/c) ∏_{w ∈ W, w ≥ c} (1 - y/(w + 1))`. -/
theorem eval_confPolyP_ins {W : Finset ℕ} {c : ℕ} (hc : c ∉ W) (y : ℝ) :
    (confPolyP (ins W c)).eval y = (∏ w ∈ W.filter (· < c), (1 - y / w)) * (1 - y / c) *
      ∏ w ∈ W.filter (c ≤ ·), (1 - y / ((w : ℝ) + 1)) := by
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
  rw [eval_confPolyP, ins, Finset.prod_union hdisj, Finset.prod_insert hnot,
    Finset.prod_image fun a _ b _ h => by simpa only [add_left_inj] using h, mul_assoc]
  push_cast

/-- For `0 ≤ s` and integers `c ≥ s`, the factors `g(w) = 1 + s/((w - s)(w + 1))` over a
set `U` of integers above `c` multiply to at most
`(c + 1)/(c + 1 - s) · (c + 1 + |U| - s)/(c + 1 + |U|)`. -/
theorem prod_g_le {s : ℝ} (hs : 0 ≤ s) {c : ℕ} (hsc : s < c + 1) :
    ∀ U : Finset ℕ, (∀ w ∈ U, c < w) →
      ∏ w ∈ U, (1 + s / (((w : ℝ) - s) * (w + 1))) ≤
        (c + 1) / (c + 1 - s) * ((c + 1 + U.card - s) / (c + 1 + U.card)) := by
  classical
  intro U
  induction U using Finset.induction_on_max with
  | h0 =>
    intro _
    have h1 : (c : ℝ) + 1 - s ≠ 0 := by linarith
    have h2 : (c : ℝ) + 1 ≠ 0 := by positivity
    rw [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, add_zero, div_mul_div_comm,
      mul_comm ((c : ℝ) + 1), div_self (mul_ne_zero h1 h2)]
  | step a U hlt ih =>
    intro hU
    have haU : a ∉ U := fun h => lt_irrefl a (hlt a h)
    have hU' := ih fun w hw => hU w (Finset.mem_insert_of_mem hw)
    have hca := hU a (Finset.mem_insert_self a U)
    set m := U.card
    have hma : c + m + 1 ≤ a := by
      have := Finset.card_le_card (show U ⊆ Finset.Ioo c a from fun w hw =>
        Finset.mem_Ioo.2 ⟨hU w (Finset.mem_insert_of_mem hw), hlt w hw⟩)
      rw [Nat.card_Ioo] at this
      omega
    rw [Finset.prod_insert haU, Finset.card_insert_of_notMem haU]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hw1 : ((c + m + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast hma
    push_cast at hw1
    -- `g` decreases, so `g(a) ≤ g(c + m + 1)`
    have hga : 1 + s / (((a : ℝ) - s) * (a + 1)) ≤
        1 + s / ((((c : ℝ) + m + 1) - s) * ((c : ℝ) + m + 1 + 1)) := by
      have hd : 0 < (((c : ℝ) + m + 1) - s) * ((c : ℝ) + m + 1 + 1) := by
        have : 0 < ((c : ℝ) + m + 1) - s := by linarith
        positivity
      have : (((c : ℝ) + m + 1) - s) * ((c : ℝ) + m + 1 + 1) ≤ ((a : ℝ) - s) * (a + 1) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      linarith [div_le_div_of_nonneg_left hs hd this]
    have hg0 : 0 ≤ 1 + s / (((a : ℝ) - s) * (a + 1)) := by
      have : 0 < ((a : ℝ) - s) * (a + 1) := by
        have : (0 : ℝ) < a - s := by linarith
        positivity
      positivity
    have hG0 : 0 ≤ (c + 1) / (c + 1 - s) * ((c + 1 + m - s) / (c + 1 + m)) := by
      have : (0 : ℝ) < c + 1 - s := by linarith
      have : (0 : ℝ) < c + 1 + m - s := by linarith
      positivity
    calc (1 + s / (((a : ℝ) - s) * (a + 1))) * ∏ w ∈ U, (1 + s / (((w : ℝ) - s) * (w + 1)))
        ≤ (1 + s / ((((c : ℝ) + m + 1) - s) * ((c : ℝ) + m + 1 + 1))) *
            ((c + 1) / (c + 1 - s) * ((c + 1 + m - s) / (c + 1 + m))) :=
          mul_le_mul hga hU' (Finset.prod_nonneg fun w hw => by
            have := hU w (Finset.mem_insert_of_mem hw)
            have : (0 : ℝ) < w - s := by
              have : ((c : ℝ) + 1) ≤ w := by exact_mod_cast this
              linarith
            positivity) (by linarith)
      _ = (c + 1) / (c + 1 - s) *
            ((c + 1 + ((m + 1 : ℕ) : ℝ) - s) / (c + 1 + ((m + 1 : ℕ) : ℝ))) := by
          have h1 : (c : ℝ) + 1 - s ≠ 0 := by linarith
          have h2 : (c : ℝ) + 1 + m ≠ 0 := by positivity
          have h3 : (c : ℝ) + m + 1 - s ≠ 0 := by linarith
          have h4 : (c : ℝ) + m + 1 + 1 ≠ 0 := by positivity
          push_cast
          field_simp
          ring

/-- For `1 ≤ s < c` (integers) with `c ∉ W`, `|r_{ins(W, c)}(s)| ≤ |r_W(s)|`. -/
theorem abs_ins_le_below {W : Finset ℕ} {c s : ℕ} (hc : c ∉ W) (hs : 1 ≤ s) (hsc : s < c) :
    |(confPolyP (ins W c)).eval (s : ℝ)| ≤ |(confPolyP W).eval (s : ℝ)| := by
  classical
  set U := W.filter (c ≤ ·)
  have hU : ∀ w ∈ U, c < w := fun w hw => by
    obtain ⟨hwW, hcw⟩ := Finset.mem_filter.1 hw
    exact lt_of_le_of_ne hcw fun h => hc (h ▸ hwW)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsc' : (s : ℝ) < c := by exact_mod_cast hsc
  have hw : ∀ w ∈ U, (s : ℝ) < w := fun w hw => by
    have := hU w hw
    exact_mod_cast (show s < w by omega)
  -- factor by factor
  have hfac : ∀ w ∈ U, 1 - (s : ℝ) / ((w : ℝ) + 1) =
      (1 - (s : ℝ) / w) * (1 + s / (((w : ℝ) - s) * (w + 1))) := fun w hw => by
    have h1 : (0 : ℝ) < w - s := by linarith [hw w hw]
    have h2 : (0 : ℝ) < w := by linarith [hw w hw]
    field_simp
    ring
  rw [eval_confPolyP_ins hc, eval_confPolyP_split W c, Finset.prod_congr rfl hfac,
    Finset.prod_mul_distrib, abs_mul, abs_mul, abs_mul, abs_mul]
  have hB : 0 ≤ ∏ w ∈ U, (1 - (s : ℝ) / w) := Finset.prod_nonneg fun w hw => by
    have := hw w hw
    have : (s : ℝ) / w ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hg := prod_g_le (by linarith) (show (s : ℝ) < c + 1 by linarith) U hU
  have hG : ∏ w ∈ U, (1 + (s : ℝ) / (((w : ℝ) - s) * (w + 1))) ≤ (c + 1) / (c + 1 - s) := by
    refine hg.trans (mul_le_of_le_one_right ?_ ?_)
    · have : (0 : ℝ) < c + 1 - s := by linarith
      positivity
    · rw [div_le_one (by positivity)]
      linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcs : |1 - (s : ℝ) / c| = (c - s) / c := by
    rw [abs_of_nonneg (by rw [sub_nonneg, div_le_one hc0]; linarith), one_sub_div hc0.ne']
  rw [hcs, abs_of_nonneg hB, abs_of_nonneg (Finset.prod_nonneg fun w hw => by
    have := hw w hw
    have : (0 : ℝ) < w - s := by linarith
    positivity)]
  have hcs1 : (0 : ℝ) < c + 1 - s := by linarith
  have hkey : (c - s) / c * ((c + 1) / (c + 1 - s)) ≤ (1 : ℝ) := by
    rw [div_mul_div_comm, div_le_one (by positivity)]
    nlinarith
  have hA := abs_nonneg (∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w))
  have hcs0 : 0 ≤ ((c : ℝ) - s) / c := div_nonneg (by linarith) hc0.le
  calc |∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w)| * ((c - s) / c) *
        ((∏ w ∈ U, (1 - (s : ℝ) / w)) * ∏ w ∈ U, (1 + (s : ℝ) / (((w : ℝ) - s) * (w + 1))))
      ≤ |∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w)| * ((c - s) / c) *
          ((∏ w ∈ U, (1 - (s : ℝ) / w)) * ((c + 1) / (c + 1 - s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hB) (mul_nonneg hA hcs0)
    _ = |∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w)| * (∏ w ∈ U, (1 - (s : ℝ) / w)) *
          ((c - s) / c * ((c + 1) / (c + 1 - s))) := by ring
    _ ≤ |∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w)| * (∏ w ∈ U, (1 - (s : ℝ) / w)) * 1 :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg hA hB)
    _ = _ := by rw [mul_one]

/-- `(1 - s/w)(1 - s/(w + 1)) ≥ 0` for integers `s ≥ 0`, `w ≥ 1`. -/
theorem consecutive_factors_nonneg {s w : ℕ} (hw : 1 ≤ w) :
    0 ≤ (1 - (s : ℝ) / w) * (1 - (s : ℝ) / ((w : ℝ) + 1)) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rcases le_or_gt s w with h | h
  · have h1 : (s : ℝ) ≤ w := by exact_mod_cast h
    refine mul_nonneg ?_ ?_
    · rw [sub_nonneg, div_le_one (by linarith)]; exact h1
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · have h1 : (w : ℝ) + 1 ≤ s := by exact_mod_cast h
    refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
    · rw [sub_nonpos, le_div_iff₀ (by linarith)]; linarith
    · rw [sub_nonpos, le_div_iff₀ (by linarith)]; linarith

/-- Below `c`, `r_W(s) r_{ins(W, c)}(s) ≥ 0`. -/
theorem ins_sign_below {W : Finset ℕ} {c s : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hsc : s < c) :
    0 ≤ (confPolyP W).eval (s : ℝ) * (confPolyP (ins W c)).eval (s : ℝ) := by
  classical
  rw [eval_confPolyP_ins hc, eval_confPolyP_split W c]
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have h1 : 0 ≤ 1 - (s : ℝ) / c := by
    rw [sub_nonneg, div_le_one hc0]; exact_mod_cast hsc.le
  have hB : 0 ≤ (∏ w ∈ W.filter (c ≤ ·), (1 - (s : ℝ) / w)) *
      ∏ w ∈ W.filter (c ≤ ·), (1 - (s : ℝ) / ((w : ℝ) + 1)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_nonneg fun w hw => consecutive_factors_nonneg
      (Nat.pos_of_ne_zero fun h => h0 (h ▸ (Finset.mem_filter.1 hw).1))
  have := mul_nonneg (mul_self_nonneg (∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w)))
    (mul_nonneg h1 hB)
  nlinarith

/-- Above `c`, `r_W(s) r_{ins(W, c)}(s) ≤ 0`. -/
theorem ins_sign_above {W : Finset ℕ} {c s : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hc1 : 1 ≤ c)
    (hsc : c < s) :
    (confPolyP W).eval (s : ℝ) * (confPolyP (ins W c)).eval (s : ℝ) ≤ 0 := by
  classical
  rw [eval_confPolyP_ins hc, eval_confPolyP_split W c]
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
  have h1 : 1 - (s : ℝ) / c ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hc0, one_mul]; exact_mod_cast hsc.le
  have hB : 0 ≤ (∏ w ∈ W.filter (c ≤ ·), (1 - (s : ℝ) / w)) *
      ∏ w ∈ W.filter (c ≤ ·), (1 - (s : ℝ) / ((w : ℝ) + 1)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_nonneg fun w hw => consecutive_factors_nonneg
      (Nat.pos_of_ne_zero fun h => h0 (h ▸ (Finset.mem_filter.1 hw).1))
  have := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_self_nonneg (∏ w ∈ W.filter (· < c), (1 - (s : ℝ) / w))) hB) h1
  nlinarith

end CoefficientMass
