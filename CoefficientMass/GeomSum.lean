/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowCert

/-!
# Polynomial Sums Against `2^{-t}`

This module collects the discrete tool behind Lemma 4.6 of
`coefficient-mass.tex`.  For a real polynomial `p` put
`S[p] = ∑_{t ≥ 0} p(t) 2^{-t}`.  Shifting the argument gives
`S[p(· + 1)] = 2 S[p] - 2 p(0)`, which evaluates `S[t q_k] = (k + 1) S[q_k]`
on the rising product `q_k(t) = ∏_{a ≤ k} (t + a)`.  For a set `A` of `k`
positive integers, `S[(t - c) ∏_{a ∈ A} (t + a)] ≤ 0` once `c ≥ k + 1`: the
sum is affine in each `a`, with slope of the same form on `k - 1` factors, so
lowering an element of `A` above `k` to a missing element of `{1, …, k}`
does not decrease it, and `A = {1, …, k}` is the case just evaluated.

## Definitions

* `geomSum`.
* `risingP`.

## Theorems

* `summable_geomSum`.
* `geomSum_add`.
* `geomSum_sub`.
* `geomSum_C_mul`.
* `geomSum_nonneg`.
* `geomSum_pos`.
* `geomSum_comp`.
* `eval_risingP_pos`.
* `comp_X_mul_risingP`.
* `geomSum_X_mul_risingP`.
* `geomSum_exchange`.
* `geomSum_sub_mul_risingP_nonpos`.
-/

open Polynomial

namespace CoefficientMass

/-- `S[p] = ∑_{t ≥ 0} p(t) 2^{-t}`. -/
noncomputable def geomSum (p : ℝ[X]) : ℝ :=
  ∑' t : ℕ, p.eval (t : ℝ) * (1 / 2) ^ t

/-- The rising product `∏_{a ∈ A} (t + a)`. -/
noncomputable def risingP (A : Finset ℕ) : ℝ[X] :=
  ∏ a ∈ A, (X + C (a : ℝ))

theorem summable_geomSum (p : ℝ[X]) :
    Summable fun t : ℕ => p.eval (t : ℝ) * (1 / 2 : ℝ) ^ t := by
  refine (summable_sum fun i (_ : i ∈ Finset.range (p.natDegree + 1)) =>
    (summable_pow_mul_geometric_of_norm_lt_one i
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (p.coeff i)).congr fun t => ?_
  rw [eval_eq_sum_range, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem geomSum_add (p q : ℝ[X]) : geomSum (p + q) = geomSum p + geomSum q := by
  rw [geomSum, geomSum, geomSum, ← (summable_geomSum p).tsum_add (summable_geomSum q)]
  exact tsum_congr fun t => by rw [eval_add, add_mul]

theorem geomSum_sub (p q : ℝ[X]) : geomSum (p - q) = geomSum p - geomSum q := by
  rw [geomSum, geomSum, geomSum, ← (summable_geomSum p).tsum_sub (summable_geomSum q)]
  exact tsum_congr fun t => by rw [eval_sub, sub_mul]

theorem geomSum_C_mul (a : ℝ) (p : ℝ[X]) : geomSum (C a * p) = a * geomSum p := by
  rw [geomSum, geomSum, ← tsum_mul_left]
  exact tsum_congr fun t => by rw [eval_mul, eval_C, mul_assoc]

theorem geomSum_nonneg {p : ℝ[X]} (h : ∀ t : ℕ, 0 ≤ p.eval (t : ℝ)) : 0 ≤ geomSum p :=
  tsum_nonneg fun t => mul_nonneg (h t) (by positivity)

theorem geomSum_pos {p : ℝ[X]} (h : ∀ t : ℕ, 0 ≤ p.eval (t : ℝ)) (h0 : 0 < p.eval 0) :
    0 < geomSum p := by
  have h1 : 0 < p.eval ((0 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 0 := by
    rw [Nat.cast_zero, pow_zero, mul_one]
    exact h0
  exact h1.trans_le ((summable_geomSum p).le_tsum 0 fun t _ => mul_nonneg (h t) (by positivity))

/-- The shift `S[p(· + 1)] = 2 S[p] - 2 p(0)`. -/
theorem geomSum_comp (p : ℝ[X]) :
    geomSum (p.comp (X + 1)) = 2 * geomSum p - 2 * p.eval 0 := by
  have e : ∀ t : ℕ, p.eval ((t + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (t + 1) =
      1 / 2 * ((p.comp (X + 1)).eval (t : ℝ) * (1 / 2) ^ t) := fun t => by
    rw [eval_comp, eval_add, eval_X, eval_one]
    push_cast
    ring
  rw [geomSum, geomSum, (summable_geomSum p).tsum_eq_zero_add, tsum_congr e, tsum_mul_left,
    Nat.cast_zero, pow_zero, mul_one]
  ring

theorem eval_risingP_pos {A : Finset ℕ} (h0 : 0 ∉ A) {x : ℝ} (hx : 0 ≤ x) :
    0 < (risingP A).eval x := by
  rw [risingP, eval_prod]
  refine Finset.prod_pos fun a ha => ?_
  have h1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ ha)
  rw [eval_add, eval_X, eval_C]
  linarith

theorem comp_X_mul_risingP (k : ℕ) :
    (X * risingP (Finset.Icc 1 k)).comp (X + 1) =
      risingP (Finset.Icc 1 k) * (X + C ((k : ℝ) + 1)) := by
  induction k with
  | zero =>
    rw [risingP, Finset.Icc_eq_empty_of_lt (by norm_num), Finset.prod_empty, mul_one, X_comp,
      one_mul, Nat.cast_zero, zero_add, C_1]
  | succ k ih =>
    rw [risingP, Finset.prod_Icc_succ_top (by omega), ← risingP, ← mul_assoc, mul_comp, ih]
    simp only [add_comp, X_comp, C_comp, one_comp, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- `S[t q_k] = (k + 1) S[q_k]`. -/
theorem geomSum_X_mul_risingP (k : ℕ) :
    geomSum (X * risingP (Finset.Icc 1 k)) = (k + 1) * geomSum (risingP (Finset.Icc 1 k)) := by
  have h := geomSum_comp (X * risingP (Finset.Icc 1 k))
  have e : risingP (Finset.Icc 1 k) * (X + C ((k : ℝ) + 1)) =
      X * risingP (Finset.Icc 1 k) + C ((k : ℝ) + 1) * risingP (Finset.Icc 1 k) := by ring
  rw [comp_X_mul_risingP, e, geomSum_add, geomSum_C_mul, eval_mul, eval_X, zero_mul] at h
  linarith

/-- Replacing `a ∈ A` by `b ∉ A` changes the sum by `(a - b)` times the sum on `A \ {a}`. -/
theorem geomSum_exchange {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∉ A) (c : ℝ) :
    geomSum ((X - C c) * risingP A) = geomSum ((X - C c) * risingP (insert b (A.erase a))) +
      ((a : ℝ) - b) * geomSum ((X - C c) * risingP (A.erase a)) := by
  have hb' : b ∉ A.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [risingP, risingP, risingP, ← Finset.mul_prod_erase A _ ha, Finset.prod_insert hb',
    ← risingP, ← geomSum_C_mul, ← geomSum_add, map_sub]
  congr 1
  ring

/-- `S[(t - c) ∏_{a ∈ A} (t + a)] ≤ 0` for `A ⊂ ℕ_{>0}` with `|A| = k` and `c ≥ k + 1`. -/
theorem geomSum_sub_mul_risingP_nonpos : ∀ (k s : ℕ) (A : Finset ℕ), A.card = k →
    A.sum id = s → 0 ∉ A → ∀ c : ℝ, (k : ℝ) + 1 ≤ c → geomSum ((X - C c) * risingP A) ≤ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihcard =>
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihsum =>
  intro A hk hs h0 c hc
  by_cases hA : ∀ a ∈ A, a ≤ k
  · have hE : A = Finset.Icc 1 k := Finset.eq_of_subset_of_card_le
      (fun a ha => Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ ha), hA a ha⟩)
      (by rw [Nat.card_Icc, hk]; omega)
    have hR := geomSum_nonneg fun t : ℕ =>
      (eval_risingP_pos (A := Finset.Icc 1 k) (fun h => by
        have := (Finset.mem_Icc.1 h).1
        omega)
        (Nat.cast_nonneg t)).le
    rw [hE, sub_mul, geomSum_sub, geomSum_C_mul, geomSum_X_mul_risingP]
    nlinarith
  push_neg at hA
  obtain ⟨a, ha, hka⟩ := hA
  obtain ⟨b, hbI, hb⟩ : ∃ b ∈ Finset.Icc 1 k, b ∉ A := by
    by_contra hb
    push_neg at hb
    have haI : a ∉ Finset.Icc 1 k := fun h => by
      have := (Finset.mem_Icc.1 h).2
      omega
    have := Finset.card_le_card (Finset.insert_subset ha hb)
    rw [Finset.card_insert_of_notMem haI, Nat.card_Icc] at this
    omega
  obtain ⟨hb1, hbk⟩ := Finset.mem_Icc.1 hbI
  have hk1 : 1 ≤ k := by
    have := Finset.card_pos.2 ⟨a, ha⟩
    omega
  have h0e : 0 ∉ A.erase a := fun h => h0 (Finset.mem_of_mem_erase h)
  have hce : (A.erase a).card = k - 1 := by rw [Finset.card_erase_of_mem ha, hk]
  have hb' : b ∉ A.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  have hkk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have h1 := ihcard (k - 1) (by omega) _ (A.erase a) hce rfl h0e c (by linarith)
  have hsum : (insert b (A.erase a)).sum id < s := by
    rw [Finset.sum_insert hb', ← hs, ← Finset.add_sum_erase A id ha]
    simp only [id_eq]
    omega
  have h2 := ihsum _ hsum (insert b (A.erase a))
    (by rw [Finset.card_insert_of_notMem hb', hce]; omega) rfl
    (fun h => by
      rcases Finset.mem_insert.1 h with h | h
      · omega
      · exact h0e h) c hc
  have hab : (0 : ℝ) ≤ (a : ℝ) - b := by
    have : (b : ℝ) ≤ a := by exact_mod_cast (hbk.trans hka.le)
    linarith
  rw [geomSum_exchange ha hb c]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hab h1]

end CoefficientMass
