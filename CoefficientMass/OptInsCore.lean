/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OptInsDir

/-!
# The Inequality Behind Lemma 5.2

This module proves Steps 3 and 4 of Lemma 5.2 of `coefficient-mass-rows.tex` for a finite
truncation `D`, abstracted over the values `p(s) = P(s)` and `q(s) = Q(s)`.  With
`w(s) = r^{-s}` and `α(s) = 1 + ε - εκs ≥ ε`, the sign pattern makes `|α p - ε q| w` equal to
`α |p| w ∓ ε |q| w` on either side of `c`, so the optimality of `P` in the direction
`(α - 1) P - ε Q` gives `κ M + Φ^{<c}(q) ≤ φ + Φ^{≥c}(q)` exactly, with `M = ∑ s |p(s)| w(s)`.
The shift bound `|q(u + 1)| ≤ κ u |p(u)|` then gives `(r - 1) Φ(q) ≤ φ + (r - 2) Φ^{<c}(q)`.

## Theorems

* `sum_Icc_shift_le`.
* `sum_split_lt`.
* `opt_core_step`.
* `opt_core`.
-/

namespace CoefficientMass

/-- With `f ≥ 0` and `f(c) = 0`: `∑_{s = c}^{D} f(s) ≤ ∑_{u = c}^{D} f(u + 1)`. -/
theorem sum_Icc_shift_le {f : ℕ → ℝ} (hf : ∀ s, 0 ≤ f s) {c D : ℕ} (hc : f c = 0) :
    ∑ s ∈ Finset.Icc c D, f s ≤ ∑ u ∈ Finset.Icc c D, f (u + 1) := by
  have hsub : Finset.Icc c D ⊆ insert c (Finset.Icc (c + 1) (D + 1)) := fun s hs => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hs
    rcases h1.eq_or_lt with h | h
    · exact h ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.2 ⟨h, by omega⟩)
  have hnot : c ∉ Finset.Icc (c + 1) (D + 1) := fun h => by
    have := (Finset.mem_Icc.1 h).1
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => hf s).trans_eq ?_
  rw [Finset.sum_insert hnot, hc, zero_add, ← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- `∑_I f = ∑_{I, s < c} f + ∑_{I, s ≥ c} f`. -/
theorem sum_split_lt (I : Finset ℕ) (c : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ I, f s = ∑ s ∈ I.filter (· < c), f s + ∑ s ∈ I.filter (c ≤ ·), f s := by
  rw [← Finset.sum_filter_add_sum_filter_not I (· < c)]
  congr 1
  exact Finset.sum_congr (Finset.filter_congr fun x _ => not_lt) fun _ _ => rfl

/-- Step 3: the optimality of `p` in one direction gives
`κ M + Φ^{<c}(q) ≤ φ + Φ^{≥c}(q)`. -/
theorem opt_core_step {w p q : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ) {c D : ℕ}
    (hbelow : ∀ s, 1 ≤ s → s < c → 0 ≤ p s * q s ∧ |q s| ≤ |p s|)
    (habove : ∀ s, c ≤ s → p s * q s ≤ 0)
    (hopt : ∀ ε : ℝ, ∑ s ∈ Finset.Icc 1 D, |p s| * w s ≤
      ∑ s ∈ Finset.Icc 1 D, |(1 + ε - ε * κ * s) * p s - ε * q s| * w s) :
    κ * ∑ s ∈ Finset.Icc 1 D, s * |p s| * w s +
        ∑ s ∈ (Finset.Icc 1 D).filter (· < c), |q s| * w s ≤
      ∑ s ∈ Finset.Icc 1 D, |p s| * w s + ∑ s ∈ (Finset.Icc 1 D).filter (c ≤ ·), |q s| * w s := by
  set I := Finset.Icc 1 D
  set ε : ℝ := 1 / (κ * (D + 1)) with hεdef
  have hε : 0 < ε := div_pos one_pos (mul_pos hκ (by positivity))
  have hεκ : ε * κ * (D + 1) = 1 := by
    have : (D : ℝ) + 1 ≠ 0 := by positivity
    have := hκ.ne'
    rw [hεdef]
    field_simp
  have hαε : ∀ s ∈ I, ε ≤ 1 + ε - ε * κ * s := fun s hs => by
    have hsD : (s : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.1 hs).2
    have := mul_le_mul_of_nonneg_left hsD (mul_pos hε hκ).le
    linarith [mul_pos hε hκ]
  have e1 : ∑ s ∈ I.filter (· < c), |(1 + ε - ε * κ * s) * p s - ε * q s| * w s =
      (1 + ε) * ∑ s ∈ I.filter (· < c), |p s| * w s -
        ε * κ * ∑ s ∈ I.filter (· < c), s * |p s| * w s -
        ε * ∑ s ∈ I.filter (· < c), |q s| * w s := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsI, hsc⟩ := Finset.mem_filter.1 hs
    obtain ⟨hpq, hqp⟩ := hbelow s (Finset.mem_Icc.1 hsI).1 hsc
    rw [abs_sub_same_sign hpq hqp hε.le (hαε s hsI)]
    ring
  have e2 : ∑ s ∈ I.filter (c ≤ ·), |(1 + ε - ε * κ * s) * p s - ε * q s| * w s =
      (1 + ε) * ∑ s ∈ I.filter (c ≤ ·), |p s| * w s -
        ε * κ * ∑ s ∈ I.filter (c ≤ ·), s * |p s| * w s +
        ε * ∑ s ∈ I.filter (c ≤ ·), |q s| * w s := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsI, hsc⟩ := Finset.mem_filter.1 hs
    rw [abs_sub_opp_sign (habove s hsc) (hε.le.trans (hαε s hsI)) hε.le]
    ring
  have s1 : ∑ s ∈ I, |p s| * w s =
      ∑ s ∈ I.filter (· < c), |p s| * w s + ∑ s ∈ I.filter (c ≤ ·), |p s| * w s :=
    sum_split_lt I c _
  have s2 : ∑ s ∈ I, s * |p s| * w s =
      ∑ s ∈ I.filter (· < c), s * |p s| * w s + ∑ s ∈ I.filter (c ≤ ·), s * |p s| * w s :=
    sum_split_lt I c _
  have s3 : ∑ s ∈ I, |(1 + ε - ε * κ * s) * p s - ε * q s| * w s =
      ∑ s ∈ I.filter (· < c), |(1 + ε - ε * κ * s) * p s - ε * q s| * w s +
        ∑ s ∈ I.filter (c ≤ ·), |(1 + ε - ε * κ * s) * p s - ε * q s| * w s :=
    sum_split_lt I c _
  have h := hopt ε
  have key : ε * (κ * ∑ s ∈ I, s * |p s| * w s + ∑ s ∈ I.filter (· < c), |q s| * w s) ≤
      ε * (∑ s ∈ I, |p s| * w s + ∑ s ∈ I.filter (c ≤ ·), |q s| * w s) := by
    rw [s1, s2]
    rw [s3, e1, e2, s1] at h
    linarith
  exact le_of_mul_le_mul_left key hε

/-- Steps 2 and 4 of Lemma 5.2 of `coefficient-mass-rows.tex` for values `p, q` on `[1, D]`. -/
theorem opt_core {p q : ℕ → ℝ} {r κ : ℝ} (hr : 1 < r) (hκ : 0 < κ) {c D : ℕ} (hc1 : 1 ≤ c)
    (hbelow : ∀ s, 1 ≤ s → s < c → 0 ≤ p s * q s ∧ |q s| ≤ |p s|)
    (habove : ∀ s, c ≤ s → p s * q s ≤ 0) (hc0 : q c = 0)
    (hshift : ∀ u : ℕ, c ≤ u → |q (u + 1)| ≤ κ * u * |p u|)
    (hopt : ∀ ε : ℝ, ∑ s ∈ Finset.Icc 1 D, |p s| * (1 / r) ^ s ≤
      ∑ s ∈ Finset.Icc 1 D, |(1 + ε - ε * κ * s) * p s - ε * q s| * (1 / r) ^ s) :
    (r - 1) * ∑ s ∈ Finset.Icc 1 D, |q s| * (1 / r) ^ s ≤
      ∑ s ∈ Finset.Icc 1 D, |p s| * (1 / r) ^ s +
        (r - 2) * ∑ s ∈ (Finset.Icc 1 D).filter (· < c), |q s| * (1 / r) ^ s := by
  set I := Finset.Icc 1 D
  have hr0 : r ≠ 0 := (by linarith : (0 : ℝ) < r).ne'
  have hw : ∀ n : ℕ, 0 ≤ (1 / r) ^ n := fun n => pow_nonneg (one_div_nonneg.2 (by linarith)) n
  have hstep := opt_core_step (w := fun s => (1 / r) ^ s) hκ hbelow habove hopt
  have hfilt : I.filter (c ≤ ·) = Finset.Icc c D := by
    ext s
    simp only [I, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨by omega, h.2⟩, h.1⟩⟩
  rw [hfilt] at hstep
  -- Step 2: the shift
  have hS2 : ∑ s ∈ Finset.Icc c D, |q s| * (1 / r) ^ s ≤
      κ / r * ∑ s ∈ Finset.Icc c D, s * |p s| * (1 / r) ^ s := by
    refine (sum_Icc_shift_le (f := fun s => |q s| * (1 / r) ^ s)
      (fun s => mul_nonneg (abs_nonneg _) (hw s)) (by simp only [hc0, abs_zero, zero_mul])).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    calc |q (u + 1)| * (1 / r) ^ (u + 1) ≤ κ * u * |p u| * (1 / r) ^ (u + 1) :=
          mul_le_mul_of_nonneg_right (hshift u (Finset.mem_Icc.1 hu).1) (hw _)
      _ = κ / r * (u * |p u| * (1 / r) ^ u) := by ring
  have hM : ∑ s ∈ I, s * |p s| * (1 / r) ^ s = ∑ s ∈ I.filter (· < c), s * |p s| * (1 / r) ^ s +
      ∑ s ∈ Finset.Icc c D, s * |p s| * (1 / r) ^ s := by
    rw [← hfilt]
    exact sum_split_lt I c _
  have hQ : ∑ s ∈ I, |q s| * (1 / r) ^ s = ∑ s ∈ I.filter (· < c), |q s| * (1 / r) ^ s +
      ∑ s ∈ Finset.Icc c D, |q s| * (1 / r) ^ s := by
    rw [← hfilt]
    exact sum_split_lt I c _
  have hM1 : 0 ≤ κ * ∑ s ∈ I.filter (· < c), s * |p s| * (1 / r) ^ s :=
    mul_nonneg hκ.le (Finset.sum_nonneg fun s _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (hw s))
  have hκM : κ * ∑ s ∈ I, s * |p s| * (1 / r) ^ s =
      κ * ∑ s ∈ I.filter (· < c), s * |p s| * (1 / r) ^ s +
        κ * ∑ s ∈ Finset.Icc c D, s * |p s| * (1 / r) ^ s := by
    rw [hM, mul_add]
  have hrt : r * (κ / r * ∑ s ∈ Finset.Icc c D, s * |p s| * (1 / r) ^ s) =
      κ * ∑ s ∈ Finset.Icc c D, s * |p s| * (1 / r) ^ s := by
    field_simp
  have hf1 := mul_le_mul_of_nonneg_left hS2 (by linarith : (0 : ℝ) ≤ r - 1)
  rw [hQ]
  linarith

end CoefficientMass
