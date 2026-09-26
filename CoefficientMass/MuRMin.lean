/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OnePoly
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.Compact

/-!
# Minimizers of `μ_r(S, L)`

This module proves that `μ_r(S, L)` is attained, as used in Lemma 6.11 and Theorem 6.12 of
`coefficient-mass-rows.tex`.  Write `q` through its coefficient vector `c ∈ ℝ^L`.  Lagrange
interpolation at `0, …, L - 1` bounds every coefficient by `(1 + B r^L) K_L` once
`q(0) = 1` and `Φ_r(q) ≤ B`, so a sublevel set lies in a ball; on the ball `Φ_r` is a uniform
limit of continuous functions, and a continuous function on a compact set attains its minimum.

## Definitions

* `coeffPoly`.
* `lagK`.

## Theorems

* `eval_coeffPoly`.
* `degree_coeffPoly`.
* `coeffPoly_coeff`.
* `abs_coeff_le`.
* `continuousOn_rowPhi`.
* `exists_muR_min`.
-/

open Polynomial

namespace CoefficientMass

/-- The polynomial `∑_{i < L} c_i X^i`. -/
noncomputable def coeffPoly {L : ℕ} (c : Fin L → ℝ) : ℝ[X] :=
  ∑ i : Fin L, C (c i) * X ^ (i : ℕ)

/-- `K_L = ∑_{i, j < L} |[X^i] ℓ_j|` for the Lagrange basis at `0, …, L - 1`. -/
noncomputable def lagK (L : ℕ) : ℝ :=
  ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    |((Lagrange.basis (Finset.range L) (fun j : ℕ => (j : ℝ)) j).coeff i)|

theorem eval_coeffPoly {L : ℕ} (c : Fin L → ℝ) (y : ℝ) :
    (coeffPoly c).eval y = ∑ i : Fin L, c i * y ^ (i : ℕ) := by
  simp only [coeffPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

theorem degree_coeffPoly {L : ℕ} (c : Fin L → ℝ) : (coeffPoly c).degree < L :=
  degree_sum_fin_lt c

theorem coeffPoly_coeff {L : ℕ} {q : ℝ[X]} (hq : q.degree < L) :
    coeffPoly (fun i : Fin L => q.coeff i) = q := by
  ext n
  rw [coeffPoly, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rcases lt_or_ge n L with h | h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun b _ hb => if_neg fun e => hb (Fin.ext e.symm))
      (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
  · rw [Finset.sum_eq_zero fun b _ => if_neg (by have := b.2; omega)]
    exact (coeff_eq_zero_of_degree_lt (hq.trans_le (by exact_mod_cast h))).symm

/-- `|[X^i] q| ≤ (1 + B r^L) K_L` for `deg q < L`, `q(0) = 1` and `Φ_r(q) ≤ B`. -/
theorem abs_coeff_le {r : ℝ} (hr : 1 < r) {L : ℕ} {q : ℝ[X]} (hq : q.degree < L)
    (hq0 : q.eval 0 = 1) {B : ℝ} (hB : rowPhi r q ≤ B) (i : ℕ) :
    |q.coeff i| ≤ (1 + B * r ^ L) * lagK L := by
  have hB0 : 0 ≤ B := (tsum_nonneg fun _ => by positivity).trans hB
  have hK0 : 0 ≤ lagK L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC0 : 0 ≤ 1 + B * r ^ L := by positivity
  rcases lt_or_ge i L with hi | hi
  swap
  · rw [coeff_eq_zero_of_degree_lt (hq.trans_le (by exact_mod_cast hi)), abs_zero]
    positivity
  -- every value `q(j)`, `j < L`, is at most `1 + B r^L`
  have hval : ∀ j ∈ Finset.range L, |q.eval (j : ℝ)| ≤ 1 + B * r ^ L := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.cast_zero, hq0, abs_one]
      linarith [mul_nonneg hB0 (pow_nonneg (by linarith : (0 : ℝ) ≤ r) L)]
    have hterm := (summable_rowPhi hr q).sum_le_tsum {j - 1} fun _ _ => by positivity
    rw [Finset.sum_singleton, Nat.sub_add_cancel hj0] at hterm
    have h1 : |q.eval (j : ℝ)| * (1 / r) ^ j ≤ B := hterm.trans hB
    rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)] at h1
    have h2 : r ^ j ≤ r ^ L := pow_le_pow_right₀ hr.le (Finset.mem_range.1 hj).le
    nlinarith [mul_le_mul_of_nonneg_left h2 hB0]
  have hinj : Set.InjOn (fun j : ℕ => (j : ℝ)) (Finset.range L : Set ℕ) :=
    fun a _ b _ h => by
      have h' : (a : ℝ) = b := h
      exact_mod_cast h'
  have hq' := Lagrange.eq_interpolate hinj (by rwa [Finset.card_range])
  rw [hq', Lagrange.interpolate_apply, finset_sum_coeff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range L, |(C (q.eval (j : ℝ)) *
        Lagrange.basis (Finset.range L) (fun j : ℕ => (j : ℝ)) j).coeff i|
      ≤ ∑ j ∈ Finset.range L, (1 + B * r ^ L) *
          |(Lagrange.basis (Finset.range L) (fun j : ℕ => (j : ℝ)) j).coeff i| :=
        Finset.sum_le_sum fun j hj => by
          rw [coeff_C_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (hval j hj) (abs_nonneg _)
    _ = (1 + B * r ^ L) * ∑ j ∈ Finset.range L,
          |(Lagrange.basis (Finset.range L) (fun j : ℕ => (j : ℝ)) j).coeff i| :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (1 + B * r ^ L) * lagK L :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range L,
          |(Lagrange.basis (Finset.range L) (fun j : ℕ => (j : ℝ)) j).coeff i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hi)) hC0

/-- `c ↦ Φ_r(∑ c_i X^i)` is continuous on every closed ball. -/
theorem continuousOn_rowPhi {r : ℝ} (hr : 1 < r) (L : ℕ) (R : ℝ) :
    ContinuousOn (fun c : Fin L → ℝ => rowPhi r (coeffPoly c)) (Metric.closedBall 0 R) := by
  have hx0 : 0 ≤ 1 / r := by positivity
  have hx1 : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr
  have hu : Summable fun d : ℕ => R * L * ((1 + ((d + 1 : ℕ) : ℝ)) ^ L * (1 / r) ^ (d + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_poly_geom hx0 hx1 L)).mul_left _
  change ContinuousOn (fun c : Fin L → ℝ =>
    ∑' d : ℕ, |(coeffPoly c).eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) _
  refine continuousOn_tsum (fun d => ?_) hu fun d c hc => ?_
  · have e : (fun c : Fin L → ℝ => |(coeffPoly c).eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) =
        fun c => |∑ i : Fin L, c i * (((d + 1 : ℕ) : ℝ)) ^ (i : ℕ)| * (1 / r) ^ (d + 1) :=
      funext fun c => by rw [eval_coeffPoly]
    rw [e]
    exact ((continuous_finset_sum _ fun i _ =>
      (continuous_apply i).mul continuous_const).abs.mul continuous_const).continuousOn
  · have hcR : ‖c‖ ≤ R := mem_closedBall_zero_iff.1 hc
    have hy1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d + 1 by omega)
    set y : ℝ := ((d + 1 : ℕ) : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), eval_coeffPoly]
    have hsum : |∑ i : Fin L, c i * y ^ (i : ℕ)| ≤ R * L * (1 + y) ^ L := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i : Fin L, |c i * y ^ (i : ℕ)| ≤ ∑ _i : Fin L, R * (1 + y) ^ L :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ (i : ℕ))]
              have hci : |c i| ≤ R := (norm_le_pi_norm c i).trans hcR
              have hyi : y ^ (i : ℕ) ≤ (1 + y) ^ L :=
                (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
                  (pow_le_pow_right₀ (by linarith) i.2.le)
              exact mul_le_mul hci hyi (by positivity) ((abs_nonneg _).trans hci)
        _ = R * L * (1 + y) ^ L := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc |∑ i : Fin L, c i * y ^ (i : ℕ)| * (1 / r) ^ (d + 1)
        ≤ R * L * (1 + y) ^ L * (1 / r) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = R * L * ((1 + y) ^ L * (1 / r) ^ (d + 1)) := by ring

/-- `μ_r(S, L)` is attained for `0 ∉ S` and `|S| < L`. -/
theorem exists_muR_min {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S)
    (hS : S.card < L) : ∃ q : ℝ[X], q.degree < L ∧ q.eval 0 = 1 ∧
      (∀ s ∈ S, q.eval (s : ℝ) = 0) ∧ rowPhi r q = muR r S L := by
  obtain ⟨hdeg0, h00, hS0⟩ := confPolyP_admissible (L := L) h0 hS
  set B := rowPhi r (confPolyP S)
  set R := (1 + B * r ^ L) * lagK L
  have hev : ∀ y : ℝ, Continuous fun c : Fin L → ℝ => (coeffPoly c).eval y := fun y => by
    have e : (fun c : Fin L → ℝ => (coeffPoly c).eval y) =
        fun c => ∑ i : Fin L, c i * y ^ (i : ℕ) := funext fun c => eval_coeffPoly c y
    rw [e]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  set A : Set (Fin L → ℝ) := {c | (coeffPoly c).eval 0 = 1} ∩
    ⋂ s ∈ S, {c | (coeffPoly c).eval (s : ℝ) = 0}
  have hA : IsClosed A := (isClosed_eq (hev 0) continuous_const).inter
    (isClosed_biInter fun s _ => isClosed_eq (hev _) continuous_const)
  have hmemA : ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 → (∀ s ∈ S, q.eval (s : ℝ) = 0) →
      (fun i : Fin L => q.coeff i) ∈ A := fun q hq hq0 hqS => by
    refine ⟨?_, Set.mem_iInter₂.2 fun s hs => ?_⟩
    · change (coeffPoly _).eval 0 = 1
      rw [coeffPoly_coeff hq, hq0]
    · change (coeffPoly _).eval (s : ℝ) = 0
      rw [coeffPoly_coeff hq, hqS s hs]
  have hball : ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 → rowPhi r q ≤ B →
      (fun i : Fin L => q.coeff i) ∈ Metric.closedBall 0 R := fun q hq hq0 hB => by
    have hR : 0 ≤ R := (abs_nonneg _).trans (abs_coeff_le hr hq hq0 hB 0)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    exact fun i => abs_coeff_le hr hq hq0 hB i
  set K := A ∩ Metric.closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left hA
  have hc0 : (fun i : Fin L => (confPolyP S).coeff i) ∈ K :=
    ⟨hmemA _ hdeg0 h00 hS0, hball _ hdeg0 h00 le_rfl⟩
  obtain ⟨c, hcK, hmin⟩ := hK.exists_isMinOn ⟨_, hc0⟩
    ((continuousOn_rowPhi hr L R).mono Set.inter_subset_right)
  obtain ⟨⟨hc1, hcS⟩, -⟩ := hcK
  have hcS' : ∀ s ∈ S, (coeffPoly c).eval (s : ℝ) = 0 := fun s hs =>
    Set.mem_iInter₂.1 hcS s hs
  have hbdd : BddBelow (Set.range fun q : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧
      ∀ s ∈ S, q.eval (s : ℝ) = 0} => rowPhi r q.1) := ⟨0, by
    rintro _ ⟨q, rfl⟩
    exact tsum_nonneg fun _ => by positivity⟩
  refine ⟨coeffPoly c, degree_coeffPoly c, hc1, hcS', le_antisymm ?_
    (ciInf_le hbdd ⟨coeffPoly c, degree_coeffPoly c, hc1, hcS'⟩)⟩
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, hdeg0, h00, hS0⟩⟩
  refine le_ciInf fun q => ?_
  obtain ⟨q, hq, hq0, hqS⟩ := q
  have hmin0 : rowPhi r (coeffPoly c) ≤ B := by
    have h : rowPhi r (coeffPoly c) ≤
        rowPhi r (coeffPoly fun i : Fin L => (confPolyP S).coeff i) := hmin hc0
    rwa [coeffPoly_coeff hdeg0] at h
  by_cases hqB : rowPhi r q ≤ B
  · have h : rowPhi r (coeffPoly c) ≤ rowPhi r (coeffPoly fun i : Fin L => q.coeff i) :=
      hmin ⟨hmemA q hq hq0 hqS, hball q hq hq0 hqB⟩
    rwa [coeffPoly_coeff hq] at h
  · exact hmin0.trans (not_le.1 hqB).le

end CoefficientMass
