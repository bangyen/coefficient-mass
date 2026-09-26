/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Block

/-!
# The Block Bound `(1 + ν_k(n))/(kr)`

This module proves the second bound of Lemma 6.21 of `coefficient-mass-rows.tex` and the
lemma itself.  With `p = r_Y` from Lemma 3.1 and `c = p(-1) ≥ 1`, the polynomial
`q(s) = r_{[2,k]}(s) p(s - 1)/c` is admissible for `μ_r([2, k], n + k - 1)`, and its `s`-th term
is `(1/(krc))` times `1` at `s = 1` and `ω_k(s - 1)|p(s - 1)|` for `s ≥ 2`.

## Theorems

* `rowPhi_block_eq`.
* `muR_block_le`.
* `block`.
-/

open Polynomial

namespace CoefficientMass

/-- `Φ_r(r_{[2,k]}(s) p(s - 1)/c) = (1 + A_k(p))/(krc)` for `p(0) = 1`. -/
theorem rowPhi_block_eq {r : ℝ} (hr : 1 < r) {k n : ℕ} (hk : 1 ≤ k) {p : ℝ[X]}
    (hpn : p.natDegree < n) (hp0 : p.eval 0 = 1) {c : ℝ} (hc : 0 < c) :
    rowPhi r (confPolyP (Finset.Icc 2 k) * p.comp (X - C 1) * C (1 / c)) =
      (1 + prefA r k p) / (k * r * c) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) < r := by linarith
  have hsum : Summable fun d : ℕ => prefixWeight r k d * |p.eval (d : ℝ)| :=
    summable_weighted (fun s => (prefixWeight_le hr k s).1)
      (summable_weight_pow hr (prefixWeight_le hr k) (n - 1)) _
      fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  have key : ∀ d : ℕ,
      |(confPolyP (Finset.Icc 2 k) * p.comp (X - C 1) * C (1 / c)).eval ((d + 1 : ℕ) : ℝ)| *
        (1 / r) ^ (d + 1) = 1 / (k * r * c) *
          ((if d = 0 then 1 else 0) + prefixWeight r k d * |p.eval (d : ℝ)|) := fun d => by
    have hb := abs_block_eval_mul hk (show 1 ≤ d + 1 by omega)
    rw [eval_mul, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / c)]
    have hd : ((d + 1 : ℕ) : ℝ) - 1 = d := by push_cast; ring
    rw [hd]
    set R := |(confPolyP (Finset.Icc 2 k)).eval ((d + 1 : ℕ) : ℝ)|
    have hk' := hk0.ne'
    have hr' := hr0.ne'
    have hc' := hc.ne'
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [if_pos rfl] at hb
      have hR : R = 1 / k := by rw [eq_div_iff hk']; exact hb
      rw [hR, if_pos rfl, prefixWeight_zero, zero_mul, add_zero, Nat.cast_zero, hp0, abs_one,
        zero_add, pow_one]
      field_simp
    · rw [if_neg (by omega), show d + 1 - 2 = d - 1 by omega] at hb
      have hR : R = ((d - 1).choose (k - 1) : ℝ) / k := by rw [eq_div_iff hk']; exact hb
      rw [hR, if_neg hd0.ne', zero_add, prefixWeight, if_pos hd0, pow_succ]
      field_simp
  unfold rowPhi
  rw [tsum_congr key, tsum_mul_left, (summable_of_ne_finset_zero (s := {0}) fun d hd => by
      rw [if_neg (by simpa only [Finset.mem_singleton] using hd)]).tsum_add hsum,
    tsum_ite_eq, prefA]
  ring

/-- `μ_r([2, k], n + k - 1) ≤ (1 + ν_k(n))/(kr)`. -/
theorem muR_block_le {r : ℝ} (hr : 1 < r) {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    muR r (Finset.Icc 2 k) (n + k - 1) ≤ (1 + nuR r k n) / (k * r) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkr : 0 < (k : ℝ) * r := mul_pos hk0 (by linarith)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨Y, hYk, hYc, hY⟩ := exists_far_near_nuR hr (by omega : 1 ≤ k) (by omega : 1 ≤ n)
    (mul_pos hkr hδ)
  have hY0 : 0 ∉ Y := fun h => by have := hYk 0 h; omega
  obtain ⟨hdegY, hp0, -⟩ := confPolyP_admissible (L := n) hY0 (by omega)
  have hpn : (confPolyP Y).natDegree < n := (natDegree_confPolyP Y).trans_lt (by omega)
  set p := confPolyP Y
  set c := p.eval (-1)
  have hc1 : 1 ≤ c := one_le_eval_neg_one Y
  have hc : 0 < c := by linarith
  have hA := prefA_nonneg hr k p
  -- the admissible polynomial `q`
  have hdeg : (confPolyP (Finset.Icc 2 k) * p.comp (X - C 1) * C (1 / c)).natDegree <
      n + k - 1 := by
    have h1 := natDegree_confPolyP (Finset.Icc 2 k)
    rw [Nat.card_Icc] at h1
    have h2 : (p.comp (X - C 1)).natDegree ≤ p.natDegree :=
      natDegree_comp_le.trans (by rw [natDegree_X_sub_C, mul_one])
    have h3 := natDegree_mul_le (p := confPolyP (Finset.Icc 2 k) * p.comp (X - C 1))
      (q := C (1 / c))
    have h4 := natDegree_mul_le (p := confPolyP (Finset.Icc 2 k)) (q := p.comp (X - C 1))
    rw [natDegree_C, add_zero] at h3
    omega
  have hmu : muR r (Finset.Icc 2 k) (n + k - 1) ≤
      rowPhi r (confPolyP (Finset.Icc 2 k) * p.comp (X - C 1) * C (1 / c)) := by
    unfold muR
    refine ciInf_le ⟨0, ?_⟩ (⟨_, degree_le_natDegree.trans_lt (by exact_mod_cast hdeg), ?_,
      fun s hs => ?_⟩ : {q : ℝ[X] // q.degree < ↑(n + k - 1) ∧ q.eval 0 = 1 ∧
        ∀ s ∈ Finset.Icc 2 k, q.eval (s : ℝ) = 0})
    · rintro _ ⟨q, rfl⟩
      exact tsum_nonneg fun _ => by positivity
    · have h0 : (confPolyP (Finset.Icc 2 k)).eval 0 = 1 := by
        rw [confPolyP, eval_prod]
        exact Finset.prod_eq_one fun z _ => by
          rw [eval_add, eval_mul, eval_C, eval_X, eval_C, mul_zero, zero_add]
      rw [eval_mul, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C, h0, zero_sub, one_mul]
      field_simp
    · rw [eval_mul, eval_mul, confPolyP_eval_mem hs (by
        have := (Finset.mem_Icc.1 hs).1
        omega), zero_mul, zero_mul]
  rw [rowPhi_block_eq hr (by omega) hpn hp0 hc] at hmu
  refine hmu.trans ?_
  rw [div_le_iff₀ (mul_pos hkr hc)]
  have hk' := hk0.ne'
  have hr' : r ≠ 0 := by positivity
  have hδ' : (1 + nuR r k n) / (k * r) + δ = (1 + nuR r k n + k * r * δ) / (k * r) := by
    field_simp
  rw [hδ', div_mul_eq_mul_div, le_div_iff₀ hkr]
  have hX : 0 ≤ 1 + nuR r k n + k * r * δ := by
    have := (nuR_pos hr (by omega : 1 ≤ k) (by omega : 1 ≤ n)).le
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hX hkr.le), mul_lt_mul_of_pos_right hY hkr]

theorem block : Block := by
  intro r hr n k hn hk
  have h1 := muR_block_le_prefix hr hn hk
  have h2 := muR_block_le hr hn hk
  refine ⟨h1, h2, fun hex => ?_, fun hM => ?_⟩
  · obtain ⟨q, hq, hq0, hqS, hqΦ, hq1⟩ := hex
    refine le_antisymm h1 ?_
    have e := muR_prefix hr (show 1 ≤ k + 1 by omega) (show 1 ≤ n - 1 by omega)
    rw [Nat.add_sub_cancel, show n - 1 + k = n + k - 1 by omega] at e
    rw [← e, ← hqΦ]
    unfold muR
    refine ciInf_le ⟨0, ?_⟩ (⟨q, hq, hq0, fun s hs => ?_⟩ : {q : ℝ[X] // q.degree < ↑(n + k - 1) ∧
      q.eval 0 = 1 ∧ ∀ s ∈ Finset.Icc 1 k, q.eval (s : ℝ) = 0})
    · rintro _ ⟨q, rfl⟩
      exact tsum_nonneg fun _ => by positivity
    · rcases Nat.lt_or_ge s 2 with h | h
      · rw [show s = 1 by have := (Finset.mem_Icc.1 hs).1; omega, Nat.cast_one]
        exact hq1
      · exact hqS s (Finset.mem_Icc.2 ⟨h, (Finset.mem_Icc.1 hs).2⟩)
  set M := (Finset.Icc 1 k).fold max 0 (fun i => nuR r i n)
  have hνk : nuR r k n ≤ M := (Finset.le_fold_max _).2 (Or.inr ⟨k, Finset.mem_Icc.2 ⟨by omega,
    le_rfl⟩, le_rfl⟩)
  have hν1 : nuR r 1 n ≤ M := (Finset.le_fold_max _).2 (Or.inr ⟨1, Finset.mem_Icc.2 ⟨le_rfl,
    by omega⟩, le_rfl⟩)
  have hν1pos := nuR_pos hr le_rfl (by omega : 1 ≤ n)
  have hMpos : 0 < M := hν1pos.trans_le hν1
  refine ⟨hM.trans_le h1, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkr : 0 < (k : ℝ) * r := mul_pos hk0 (by linarith)
  have hβ : rowValue r n 1 = 1 / nuR r 1 n := by
    rw [(rowValueDual r hr).2 n (by omega), muR_empty_eq hr (by omega)]
  -- `krM < 1 + M`
  have h3 : M < (1 + M) / (k * r) :=
    hM.trans_le (h2.trans (div_le_div_of_nonneg_right (by linarith) hkr.le))
  rw [lt_div_iff₀ hkr] at h3
  have h4 : 1 / M ≤ 1 / nuR r 1 n := one_div_le_one_div_of_le hν1pos hν1
  have h5 : (k : ℝ) * r - 1 < 1 / M := by
    rw [lt_div_iff₀ hMpos]
    nlinarith
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < r), hβ]
  linarith

end CoefficientMass
