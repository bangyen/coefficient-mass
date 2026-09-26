/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowDualUpper
import CoefficientMass.RowTrunc

/-!
# The Row Values as a Dual Problem

This module proves Proposition 2.1(b) of `coefficient-mass-rows.tex`,
`V_r(L, k) = inf_{|S| = k - 1} 1/μ_r(S, L)`, and the first claim of (c),
`β_r(n) = 1/μ_r(∅, n)`.  For the upper bound fix `S` and `0 < ε < μ_r(S, L)`; by the
truncation estimate some `D` has `Φ_{r,D}(q) ≥ μ_r(S, L) - ε` for every admissible `q`, and
the truncated dual then gives a monic multiple `F` of `(x - r)^L` whose magnitudes off the
`k - 1` positions at distances `S` are at most `1/(μ_r(S, L) - ε)`.

## Definitions

* `RowValueDual`.

## Theorems

* `kthMag_le_of_small`.
* `rowValue_le_kthMag`.
* `rowValue_le_inv`.
* `rowValueDual`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- Proposition 2.1(b) of `coefficient-mass-rows.tex` and the first claim of (c): for `r > 1`
and `1 ≤ k ≤ L`, `V_r(L, k) = inf_{|S| = k - 1} 1/μ_r(S, L)` over `S ⊂ ℕ_{>0}`, and
`β_r(n) = V_r(n, 1) = 1/μ_r(∅, n)` for `n ≥ 1`. -/
def RowValueDual : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ L k : ℕ, 1 ≤ k → k ≤ L →
      rowValue r L k = ⨅ S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k}, 1 / muR r S.1 L) ∧
    ∀ n : ℕ, 1 ≤ n → rowValue r n 1 = 1 / muR r ∅ n

/-- If at most the `k - 1` positions at distances `S` exceed `B`, then `b_k(F) ≤ B`. -/
theorem kthMag_le_of_small {F : ℝ[X]} {k : ℕ} (hkD : k ≤ F.natDegree) {S : Finset ℕ}
    (hSc : S.card + 1 = k) {B : ℝ}
    (hB : ∀ j < F.natDegree, F.natDegree - j ∉ S → ‖F.coeff j‖ ≤ B) : kthMag F k ≤ B := by
  by_contra hlt
  push_neg at hlt
  have hmem := kthMag_mem hkD
  set P := (Finset.range F.natDegree).filter fun j => kthMag F k ≤ ‖F.coeff j‖
  have hcount : largeCount F (kthMag F k) = P.card := rfl
  have hPS : P.card ≤ S.card := Finset.card_le_card_of_injOn (fun j => F.natDegree - j)
    (fun j hj => by
      obtain ⟨hjD, hj⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
      refine Finset.mem_coe.2 ?_
      by_contra hS
      have := hB j (Finset.mem_range.1 hjD) hS
      linarith)
    (fun i hi j hj h => by
      have := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
      have := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
      have h' : F.natDegree - i = F.natDegree - j := h
      omega)
  omega

theorem rowValue_le_kthMag {r : ℝ} {L k : ℕ} (hkL : k ≤ L) {F : ℝ[X]} (hF : F.Monic)
    (hdvd : (X - C r) ^ L ∣ F) (hk : 1 ≤ k) : rowValue r L k ≤ kthMag F k :=
  ciInf_le ⟨0, by
    rintro _ ⟨⟨G, hG, hGd⟩, rfl⟩
    exact kthMag_nonneg hk (hkL.trans (le_natDegree_of_dvd hG hGd))⟩ ⟨F, hF, hdvd⟩

/-- `V_r(L, k) ≤ 1/μ_r(S, L)` for every `S ⊂ ℕ_{>0}` with `|S| = k - 1`. -/
theorem rowValue_le_inv {r : ℝ} (hr : 1 < r) {L k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L)
    {S : Finset ℕ} (h0 : 0 ∉ S) (hSc : S.card + 1 = k) : rowValue r L k ≤ 1 / muR r S L := by
  set μ := muR r S L
  have hμ : 0 < μ := muR_pos hr h0 (by omega)
  obtain ⟨τ, hτ, hbound⟩ := rowPhi_le_trunc hr L
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, confPolyP_admissible h0 (by omega)⟩⟩
  have key : ∀ ε, 0 < ε → ε < μ → rowValue r L k ≤ 1 / (μ - ε) := by
    intro ε hε hεμ
    obtain ⟨D₁, hD₁⟩ := Metric.tendsto_atTop.1 hτ (ε / (1 + μ)) (by positivity)
    set D := max (max L D₁) (S.sup id)
    have hLD : L ≤ D := (le_max_left _ _).trans (le_max_left _ _)
    have hDD : D₁ ≤ D := (le_max_right _ _).trans (le_max_left _ _)
    have hτD : |τ D| < ε / (1 + μ) := by
      have := hD₁ D hDD
      rwa [Real.dist_eq, sub_zero] at this
    have hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ D := fun s hs =>
      ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hs),
        (Finset.le_sup (f := id) hs).trans (le_max_right _ _)⟩
    obtain ⟨F, hF, hFD, hdvd, hsmall⟩ := exists_rowPoly_small hr hS (m := μ - ε)
      (by linarith) fun q hq hq0 hqS => by
        have hΦ : μ ≤ rowPhi r q := ciInf_le ⟨0, by
          rintro _ ⟨q', rfl⟩
          exact tsum_nonneg fun _ => by
            have : 0 < 1 / r := by positivity
            positivity⟩ (⟨q, hq, hq0, hqS⟩ :
              {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})
        have hb := hbound D hLD q hq hq0
        set P := ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
        have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
        by_contra hlt
        push_neg at hlt
        have h1 : (1 + P) * τ D ≤ (1 + μ) * |τ D| := by
          have h1a : (1 + P) * τ D ≤ (1 + P) * |τ D| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
          have h1b : (1 + P) * |τ D| ≤ (1 + μ) * |τ D| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          linarith
        have h2 : (1 + μ) * |τ D| < ε := by
          rw [lt_div_iff₀ (by positivity)] at hτD
          linarith
        linarith
    refine (rowValue_le_kthMag hkL hF hdvd hk).trans (kthMag_le_of_small ?_ hSc ?_)
    · rw [hFD]
      exact hkL.trans hLD
    · rw [hFD]
      exact hsmall
  by_contra hlt
  push_neg at hlt
  set W := (1 / μ + rowValue r L k) / 2
  have hW : 1 / μ < W := by simp only [W]; linarith
  have hWV : W < rowValue r L k := by simp only [W]; linarith
  have hW0 : 0 < W := lt_trans (by positivity) hW
  have hε := key (μ - 1 / W) (by
    rw [sub_pos, div_lt_iff₀ hW0]
    rw [div_lt_iff₀ hμ] at hW
    linarith) (by
    have : 0 < 1 / W := by positivity
    linarith)
  rw [sub_sub_cancel, one_div_one_div] at hε
  linarith

theorem rowValueDual : RowValueDual := by
  intro r hr
  have hb : ∀ L k : ℕ, 1 ≤ k → k ≤ L →
      rowValue r L k = ⨅ S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k}, 1 / muR r S.1 L := by
    intro L k hk hkL
    haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k} :=
      ⟨⟨Finset.Icc 1 (k - 1), fun h => by
        have := (Finset.mem_Icc.1 h).1
        omega, by rw [Nat.card_Icc]; omega⟩⟩
    exact le_antisymm (le_ciInf fun S => rowValue_le_inv hr hk hkL S.2.1 S.2.2)
      (rowValue_ge hr hk hkL)
  refine ⟨hb, fun n hn => ?_⟩
  rw [hb n 1 le_rfl hn]
  have hS : ∀ S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = 1}, S.1 = ∅ := fun S =>
    Finset.card_eq_zero.1 (by have := S.2.2; omega)
  refine le_antisymm (ciInf_le ⟨0, ?_⟩ ⟨∅, Finset.notMem_empty 0, rfl⟩)
    (le_ciInf fun S => by rw [hS S])
  rintro _ ⟨S, rfl⟩
  exact div_nonneg zero_le_one (muR_nonneg hr _ _)

end CoefficientMass
