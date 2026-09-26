/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.IntZerosInf
import CoefficientMass.RowFar
import CoefficientMass.RowPointwise

/-!
# Prefix Values

This module sets up Section 3 of `coefficient-mass-rows.tex`.  The prefix value
`ν_i(n) = inf_p ∑_{s ≥ 1} binom(s - 1, i - 1) r^{-s} |p(s)|`, over real `p` with
`deg p < n` and `p(0) = 1`, is `μ_r([1, i - 1], n + i - 1)`, because
`|r_{[1, i - 1]}(s)| = binom(s - 1, i - 1)` for `s ≥ 1` and every admissible polynomial of
`μ_r([1, i - 1], ·)` factors through `r_{[1, i - 1]}`.  The weighted problem `Ω_k(n)` uses
`W_k(s)` in place of `binom(s - 1, i - 1)`, and `E_k(r)` collects the first `2k - 2`
positions.

## Definitions

* `prefixWeight`.
* `nuR`.
* `omegaWeight`.
* `omegaR`.
* `lossE`.

## Theorems

* `abs_confPoly_prefix`.
* `tsum_shift`.
* `summable_poly_geom`.
* `prefixWeight_le`.
* `rowPhi_prefix_mul`.
* `muR_prefix`.
-/

open Polynomial

namespace CoefficientMass

/-- `binom(s - 1, i - 1) r^{-s}` for `s ≥ 1`, and `0` at `s = 0`. -/
noncomputable def prefixWeight (r : ℝ) (i s : ℕ) : ℝ :=
  if 1 ≤ s then ((s - 1).choose (i - 1) : ℝ) * (1 / r) ^ s else 0

/-- The prefix value `ν_i(n)`. -/
noncomputable def nuR (r : ℝ) (i n : ℕ) : ℝ :=
  wInf (prefixWeight r i) n

/-- `W_k(s) r^{-s}` for `s ≥ 1`, and `0` at `s = 0`. -/
noncomputable def omegaWeight (r : ℝ) (k s : ℕ) : ℝ :=
  if 1 ≤ s then (wK k s : ℝ) * (1 / r) ^ s else 0

/-- The weighted problem `Ω_k(n)`. -/
noncomputable def omegaR (r : ℝ) (k n : ℕ) : ℝ :=
  wInf (omegaWeight r k) n

/-- The loss `E_k(r) = ∑_{s = 1}^{2k - 2} binom(s - 1, ⌊(s - 1)/2⌋) r^{-s}`. -/
noncomputable def lossE (r : ℝ) (k : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 (2 * k - 2), ((s - 1).choose ((s - 1) / 2) : ℝ) * (1 / r) ^ s

/-- `|r_{[1, j]}(s)| = binom(s - 1, j)` for `s ≥ 1`. -/
theorem abs_confPoly_prefix {s : ℕ} (hs : 1 ≤ s) :
    ∀ j : ℕ, |confPoly (Finset.Icc 1 j) s| = ((s - 1).choose j : ℝ) := by
  intro j
  induction j with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num), confPoly, Finset.prod_empty, abs_one,
      Nat.choose_zero_right, Nat.cast_one]
  | succ j ih =>
    rw [confPoly, Finset.prod_Icc_succ_top (by omega), ← confPoly, abs_mul, ih]
    have hj : (0 : ℝ) < j + 1 := by positivity
    have h := Nat.choose_succ_right_eq (s - 1) j
    rcases le_or_gt j (s - 1) with hjs | hjs
    · have hcast : ((s - 1 - j : ℕ) : ℝ) = (s : ℝ) - (j + 1) := by
        rw [Nat.cast_sub hjs, Nat.cast_sub hs]
        push_cast
        ring
      have h' : ((s - 1).choose (j + 1) : ℝ) * (j + 1) =
          ((s - 1).choose j : ℝ) * (s - (j + 1)) := by
        rw [← hcast]
        exact_mod_cast h
      have habs : |1 - (s : ℝ) / ((j + 1 : ℕ) : ℝ)| = ((s : ℝ) - (j + 1)) / (j + 1) := by
        have : (j : ℝ) + 1 ≤ s := by exact_mod_cast (show j + 1 ≤ s by omega)
        push_cast
        rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ hj]; linarith), neg_sub,
          div_sub_one hj.ne']
      rw [habs]
      field_simp
      linarith
    · rw [Nat.choose_eq_zero_of_lt hjs, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero,
        zero_mul]

/-- `∑_s g(s) = ∑_d g(d + 1)` when `g(0) = 0`. -/
theorem tsum_shift {g : ℕ → ℝ} (hg : g 0 = 0) : ∑' s, g s = ∑' d, g (d + 1) := by
  by_cases h : Summable g
  · rw [h.tsum_eq_zero_add, hg, zero_add]
  · rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable fun h' =>
      h ((summable_nat_add_iff 1).1 h')]

theorem summable_poly_geom {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    Summable fun s : ℕ => (1 + (s : ℝ)) ^ m * x ^ s := by
  have hx : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h := (summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one m hx)
  rcases hx0.eq_or_lt with h0 | h0
  · refine (summable_of_ne_finset_zero (s := {0}) fun s hs => ?_)
    rw [← h0, zero_pow (by simpa only [Finset.mem_singleton] using hs), mul_zero]
  have hx0' : x ≠ 0 := h0.ne'
  refine (h.mul_left (1 / x)).congr fun s => ?_
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- `binom(s - 1, i - 1) r^{-s} ≤ (1 + s)^{i - 1} r^{-s}`. -/
theorem prefixWeight_le {r : ℝ} (hr : 1 < r) (i s : ℕ) :
    0 ≤ prefixWeight r i s ∧ prefixWeight r i s ≤ (1 + (s : ℝ)) ^ (i - 1) * (1 / r) ^ s := by
  have hx : 0 < 1 / r := by positivity
  unfold prefixWeight
  split_ifs with hs
  · refine ⟨by positivity, mul_le_mul_of_nonneg_right ?_ (by positivity)⟩
    calc ((s - 1).choose (i - 1) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) ^ (i - 1) := by
          exact_mod_cast Nat.choose_le_pow _ _
      _ ≤ (1 + (s : ℝ)) ^ (i - 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) (by
          rw [Nat.cast_sub hs]
          push_cast
          linarith) _
  · exact ⟨le_rfl, by positivity⟩

/-- For `q = r_{[1, i - 1]} p`, `Φ_r(q) = ∑_s binom(s - 1, i - 1) r^{-s} |p(s)|`. -/
theorem rowPhi_prefix_mul (r : ℝ) {i : ℕ} {q p : ℝ[X]}
    (hfac : ∀ y : ℝ, q.eval y = (confPolyP (Finset.Icc 1 (i - 1))).eval y * p.eval y) :
    rowPhi r q = ∑' s : ℕ, prefixWeight r i s * |p.eval (s : ℝ)| := by
  rw [tsum_shift (by
    change prefixWeight r i 0 * _ = 0
    rw [prefixWeight, if_neg (by norm_num), zero_mul]), rowPhi]
  refine tsum_congr fun d => ?_
  rw [hfac, abs_mul, ← confPoly_eq_eval, abs_confPoly_prefix (by omega), prefixWeight,
    if_pos (by omega), Nat.add_sub_cancel]
  ring

/-- `ν_i(n) = μ_r([1, i - 1], n + i - 1)`. -/
theorem muR_prefix {r : ℝ} (hr : 1 < r) {i n : ℕ} (hi : 1 ≤ i) (hn : 1 ≤ n) :
    muR r (Finset.Icc 1 (i - 1)) (n + (i - 1)) = nuR r i n := by
  have h0 : 0 ∉ Finset.Icc 1 (i - 1) := fun h => by
    have := (Finset.mem_Icc.1 h).1
    omega
  have hcard : (Finset.Icc 1 (i - 1)).card = i - 1 := by rw [Nat.card_Icc]; omega
  haveI : Nonempty {q : ℝ[X] // q.degree < ↑(n + (i - 1)) ∧ q.eval 0 = 1 ∧
      ∀ s ∈ Finset.Icc 1 (i - 1), q.eval (s : ℝ) = 0} :=
    ⟨⟨_, confPolyP_admissible h0 (by omega)⟩⟩
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  have hx : 0 < 1 / r := by positivity
  refine le_antisymm (le_ciInf fun p => ?_) (le_ciInf fun q => ?_)
  · -- `r_{[1, i - 1]} p` is admissible
    obtain ⟨p, hp, hp0⟩ := p
    change _ ≤ ∑' s : ℕ, prefixWeight r i s * |p.eval (s : ℝ)|
    set q := confPolyP (Finset.Icc 1 (i - 1)) * p
    have hadm := confPolyP_admissible (L := i) h0 (by rw [hcard]; omega)
    have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
    have hpn : p.natDegree < n := by
      rw [degree_eq_natDegree hpne] at hp
      exact_mod_cast hp
    have hq : q.degree < ↑(n + (i - 1)) := by
      have : q.natDegree ≤ (i - 1) + p.natDegree :=
        (natDegree_mul_le (p := confPolyP (Finset.Icc 1 (i - 1))) (q := p)).trans
          (add_le_add ((natDegree_confPolyP _).trans hcard.le) le_rfl)
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show q.natDegree < n + (i - 1) by
        omega))
    have hq0 : q.eval 0 = 1 := by rw [eval_mul, hadm.2.1, hp0, one_mul]
    have hqS : ∀ s ∈ Finset.Icc 1 (i - 1), q.eval (s : ℝ) = 0 := fun s hs => by
      rw [eval_mul, hadm.2.2 s hs, zero_mul]
    rw [← rowPhi_prefix_mul r (q := q) fun y => eval_mul]
    exact ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by positivity⟩
      (⟨q, hq, hq0, hqS⟩ : {q : ℝ[X] // q.degree < ↑(n + (i - 1)) ∧ q.eval 0 = 1 ∧
        ∀ s ∈ Finset.Icc 1 (i - 1), q.eval (s : ℝ) = 0})
  · -- every admissible `q` factors through `r_{[1, i - 1]}`
    obtain ⟨q, hq, hq0, hqS⟩ := q
    change _ ≤ rowPhi r q
    obtain ⟨q₀, hdeg, h00, hfac⟩ := factor_conf h0 hq hq0 hqS
    rw [hcard] at hdeg
    rw [rowPhi_prefix_mul r hfac]
    exact ciInf_le ⟨0, by
      rintro _ ⟨p', rfl⟩
      exact tsum_nonneg fun s => mul_nonneg (prefixWeight_le hr i s).1 (abs_nonneg _)⟩
      (⟨q₀, degree_le_natDegree.trans_lt (by exact_mod_cast (show q₀.natDegree < n by omega)),
        h00⟩ : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})

end CoefficientMass
