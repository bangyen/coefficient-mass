/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDualLower
import Mathlib.LinearAlgebra.Lagrange

/-!
# Truncating `Φ_r`

This module proves the limit `μ_{r,D}(S, L) → μ_r(S, L)` in the proof of Proposition 2.1(b)
of `coefficient-mass-rows.tex`, in the explicit form used there.  A real `q` of degree below
`L` is the Lagrange interpolant of its values at `0, …, L - 1`; with `q(0) = 1` and
`|q(i)| ≤ r^i Φ_{r,D}(q)` for `1 ≤ i ≤ D`, this gives `|q(s)| ≤ (1 + Φ_{r,D}(q)) W(s)` for a
fixed `W` of polynomial growth, so `Φ_r(q) ≤ Φ_{r,D}(q) + (1 + Φ_{r,D}(q)) τ_D` with
`τ_D → 0`.  Interpolating at `1, …, L` instead gives `1 = |q(0)| ≤ C Φ_r(q)`, so
`μ_r(S, L) > 0`.

## Definitions

* `lagW`.

## Theorems

* `abs_eval_le_lagrange`.
* `summable_lagW`.
* `abs_eval_node_le`.
* `rowPhi_le_trunc`.
* `muR_pos`.
* `exists_trunc_ge`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `W(y) = ∑_{i < L} r^i |ℓ_i(y)|` for the Lagrange basis `ℓ_i` at `0, …, L - 1`. -/
noncomputable def lagW (r : ℝ) (L : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L,
    r ^ i * |(Lagrange.basis (Finset.range L) (fun i : ℕ => (i : ℝ)) i).eval y|

/-- `|q(y)| ≤ ∑_{i ∈ s} |q(v_i)| |ℓ_i(y)|` for `deg q < |s|`. -/
theorem abs_eval_le_lagrange {s : Finset ℕ} {v : ℕ → ℝ} (hv : Set.InjOn v s) {q : ℝ[X]}
    (hq : q.degree < s.card) (y : ℝ) :
    |q.eval y| ≤ ∑ i ∈ s, |q.eval (v i)| * |(Lagrange.basis s v i).eval y| := by
  conv_lhs => rw [Lagrange.eq_interpolate hv hq, Lagrange.interpolate_apply, eval_finset_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [eval_mul, eval_C, abs_mul]

theorem summable_lagW {r : ℝ} (hr : 1 < r) (L : ℕ) :
    Summable fun d : ℕ => lagW r L ((d + 1 : ℕ) : ℝ) * (1 / r) ^ (d + 1) := by
  simp only [lagW, Finset.sum_mul]
  exact summable_sum fun i _ => ((summable_rowPhi hr _).mul_left (r ^ i)).congr fun d => by ring

/-- A node value is at most `r^i` times a truncated sum reaching it. -/
theorem abs_eval_node_le {r : ℝ} (hr : 1 < r) (q : ℝ[X]) {i D : ℕ} (hi : 1 ≤ i) (hiD : i ≤ D) :
    |q.eval (i : ℝ)| ≤
      r ^ i * ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by
  have hmem : i - 1 ∈ Finset.range D := Finset.mem_range.2 (by omega)
  have h := Finset.single_le_sum (f := fun d => |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1))
    (fun _ _ => by positivity) hmem
  simp only [show i - 1 + 1 = i by omega] at h
  have hri : r ^ i * (1 / r) ^ i = 1 := by
    rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]
  calc |q.eval (i : ℝ)| = r ^ i * (|q.eval (i : ℝ)| * (1 / r) ^ i) := by
        rw [mul_left_comm, hri, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- `Φ_r(q) ≤ Φ_{r,D}(q) + (1 + Φ_{r,D}(q)) τ_D` with `τ_D → 0`. -/
theorem rowPhi_le_trunc {r : ℝ} (hr : 1 < r) (L : ℕ) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop (𝓝 0) ∧ ∀ D, L ≤ D → ∀ q : ℝ[X], q.degree < L →
      q.eval 0 = 1 → rowPhi r q ≤
        ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) +
          (1 + ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) * τ D := by
  set g : ℕ → ℝ := fun d => lagW r L ((d + 1 : ℕ) : ℝ) * (1 / r) ^ (d + 1)
  refine ⟨fun D => ∑' d, g (d + D), tendsto_sum_nat_add g, fun D hLD q hq hq0 => ?_⟩
  set P := ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
  have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) (Finset.range L : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  have hpt : ∀ y : ℝ, |q.eval y| ≤ (1 + P) * lagW r L y := fun y => by
    refine (abs_eval_le_lagrange hinj (by rwa [Finset.card_range]) y).trans ?_
    rw [lagW, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, Nat.cast_zero, hq0, abs_one, pow_zero, mul_one]
      linarith
    · have := abs_eval_node_le hr q h0 (hLD.trans' (Finset.mem_range.1 hi).le)
      have hri : 0 ≤ r ^ i := by positivity
      nlinarith
  have hsum := (summable_rowPhi hr q).sum_add_tsum_nat_add D
  rw [rowPhi, ← hsum]
  refine add_le_add le_rfl ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun d => ?_) ((summable_nat_add_iff D).2 (summable_rowPhi hr q))
    (((summable_nat_add_iff D).2 (summable_lagW hr L)).mul_left _)
  simp only [g]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hpt _) (by positivity)

/-- `μ_r(S, L) > 0`: interpolation at `1, …, L` bounds `1 = q(0)` by a multiple of `Φ_r(q)`. -/
theorem muR_pos {r : ℝ} (hr : 1 < r) {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S) (hS : S.card < L) :
    0 < muR r S L := by
  set C := ∑ i ∈ Finset.Icc 1 L,
    r ^ i * |(Lagrange.basis (Finset.Icc 1 L) (fun i : ℕ => (i : ℝ)) i).eval 0|
  have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) (Finset.Icc 1 L : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  have key : ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 → 1 ≤ C * rowPhi r q := fun q hq hq0 => by
    have h := abs_eval_le_lagrange hinj (by rwa [Nat.card_Icc, Nat.add_sub_cancel]) 0
    rw [hq0, abs_one] at h
    refine h.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi1 := (Finset.mem_Icc.1 hi).1
    have hnode : |q.eval (i : ℝ)| * (1 / r) ^ i ≤ rowPhi r q := by
      have := (summable_rowPhi hr q).le_tsum (i - 1) fun _ _ => by positivity
      simp only [show i - 1 + 1 = i by omega] at this
      exact this
    have hri : r ^ i * (1 / r) ^ i = 1 := by
      rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]
    have hq' : |q.eval (i : ℝ)| ≤ r ^ i * rowPhi r q := by
      calc |q.eval (i : ℝ)| = r ^ i * (|q.eval (i : ℝ)| * (1 / r) ^ i) := by
            rw [mul_left_comm, hri, mul_one]
        _ ≤ r ^ i * rowPhi r q := mul_le_mul_of_nonneg_left hnode (by positivity)
    have hb := abs_nonneg ((Lagrange.basis (Finset.Icc 1 L) (fun i : ℕ => (i : ℝ)) i).eval 0)
    nlinarith
  obtain ⟨hq, hq0, _⟩ := confPolyP_admissible h0 hS
  have hC : 0 < C := by
    have := key _ hq hq0
    have hΦ : 0 ≤ rowPhi r (confPolyP S) := tsum_nonneg fun _ => by positivity
    by_contra hC
    push_neg at hC
    nlinarith
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, confPolyP_admissible h0 hS⟩⟩
  have hle : 1 / C ≤ muR r S L := le_ciInf fun q => by
    rw [div_le_iff₀ hC, mul_comm]
    exact key q.1 q.2.1 q.2.2.1
  exact lt_of_lt_of_le (by positivity) hle

/-- Eventually `Φ_{r,M}(q) ≥ μ_r(S, L) - ε` for every `q` admissible for `μ_r(S, L)`. -/
theorem exists_trunc_ge {r : ℝ} (hr : 1 < r) (S : Finset ℕ) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀, ∀ M, M₀ ≤ M → ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 →
      (∀ s ∈ S, q.eval (s : ℝ) = 0) →
        muR r S L - ε ≤ ∑ d ∈ Finset.range M, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by
  set μ := muR r S L
  have hμ : 0 ≤ μ := muR_nonneg hr S L
  obtain ⟨τ, hτ, hbound⟩ := rowPhi_le_trunc hr L
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.1 hτ (ε / (1 + μ)) (by positivity)
  refine ⟨max L M₁, fun M hM q hq hq0 hqS => ?_⟩
  have hτM : |τ M| * (1 + μ) < ε := by
    have := hM₁ M ((le_max_right _ _).trans hM)
    rwa [Real.dist_eq, sub_zero, lt_div_iff₀ (by positivity)] at this
  have hΦ : μ ≤ rowPhi r q := ciInf_le ⟨0, by
    rintro _ ⟨q', rfl⟩
    exact tsum_nonneg fun _ => by
      have : 0 < 1 / r := by positivity
      positivity⟩ (⟨q, hq, hq0, hqS⟩ :
        {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})
  have hb := hbound M ((le_max_left _ _).trans hM) q hq hq0
  set P := ∑ d ∈ Finset.range M, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
  by_contra hlt
  push_neg at hlt
  have h1a : (1 + P) * τ M ≤ (1 + P) * |τ M| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  have h1b : (1 + P) * |τ M| ≤ (1 + μ) * |τ M| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  linarith

end CoefficientMass
