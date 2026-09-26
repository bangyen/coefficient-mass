/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowKth

/-!
# The Row Values from Below

This module proves the inequality `V_r(L, k) ≥ inf_{|S| = k - 1} 1/μ_r(S, L)` of
Proposition 2.1(b) of `coefficient-mass-rows.tex`.  If `b_k(F) < T`, fewer than `k`
nonleading magnitudes of `F` reach `T`; completing their backward distances to a set `S` of
size `k - 1`, the dual identity gives `1 ≤ T Φ_r(q)` for every `q` admissible for
`μ_r(S, L)`, so `1/μ_r(S, L) ≤ T`.

## Theorems

* `le_natDegree_of_dvd`.
* `muR_nonneg`.
* `confPolyP_admissible`.
* `inv_muR_le`.
* `rowValue_ge`.
-/

open Polynomial

namespace CoefficientMass

theorem le_natDegree_of_dvd {r : ℝ} {L : ℕ} {F : ℝ[X]} (hF : F.Monic)
    (hdvd : (X - C r) ^ L ∣ F) : L ≤ F.natDegree := by
  have := natDegree_le_of_dvd hdvd hF.ne_zero
  rwa [(monic_X_sub_C r).natDegree_pow, natDegree_X_sub_C, mul_one] at this

theorem muR_nonneg {r : ℝ} (hr : 1 < r) (S : Finset ℕ) (L : ℕ) : 0 ≤ muR r S L :=
  Real.iInf_nonneg fun q => tsum_nonneg fun _ => by
    have : 0 < 1 / r := by positivity
    positivity

/-- `r_S` is admissible for `μ_r(S, L)` when `0 ∉ S` and `|S| < L`. -/
theorem confPolyP_admissible {S : Finset ℕ} {L : ℕ} (h0 : 0 ∉ S) (hS : S.card < L) :
    (confPolyP S).degree < L ∧ (confPolyP S).eval 0 = 1 ∧
      ∀ s ∈ S, (confPolyP S).eval (s : ℝ) = 0 := by
  refine ⟨degree_le_natDegree.trans_lt ?_, ?_, fun s hs =>
    confPolyP_eval_mem hs fun h => h0 (h ▸ hs)⟩
  · exact_mod_cast (natDegree_confPolyP S).trans_lt hS
  · rw [confPolyP, eval_prod]
    exact Finset.prod_eq_one fun z _ => by rw [eval_add, eval_mul, eval_C, eval_C, eval_X]; ring

/-- If every `j < D` with `D - j ∉ S` has `‖f_j‖ ≤ T`, then `1/μ_r(S, L) ≤ T`. -/
theorem inv_muR_le {r : ℝ} (hr : 1 < r) {L : ℕ} {F : ℝ[X]} (hF : F.Monic)
    (hdvd : (X - C r) ^ L ∣ F) {S : Finset ℕ} (h0 : 0 ∉ S) (hS : S.card < L) {T : ℝ}
    (hT : 0 < T) (hsmall : ∀ j < F.natDegree, F.natDegree - j ∉ S → ‖F.coeff j‖ ≤ T) :
    1 / muR r S L ≤ T := by
  have hne : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧
      ∀ s ∈ S, q.eval (s : ℝ) = 0} := ⟨⟨_, confPolyP_admissible h0 hS⟩⟩
  have hμ : 1 / T ≤ muR r S L := by
    refine le_ciInf fun q => ?_
    obtain ⟨q, hq, hq0, hqS⟩ := q
    have h1 := one_le_mul_rowPhi hr hF hdvd hq hq0 (B := T) fun j hj hqj => by
      refine hsmall j hj fun hS' => hqj ?_
      rw [← Nat.cast_sub hj.le]
      exact hqS _ hS'
    rw [div_le_iff₀ hT, mul_comm]
    exact h1
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hμ), mul_comm]
  rwa [div_le_iff₀ hT] at hμ

/-- `V_r(L, k) ≥ inf_{|S| = k - 1} 1/μ_r(S, L)`. -/
theorem rowValue_ge {r : ℝ} (hr : 1 < r) {L k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) :
    ⨅ S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k}, 1 / muR r S.1 L ≤ rowValue r L k := by
  classical
  haveI : Nonempty {F : ℝ[X] // F.Monic ∧ (X - C r) ^ L ∣ F} :=
    ⟨⟨_, (monic_X_sub_C r).pow L, dvd_rfl⟩⟩
  refine le_ciInf fun F => ?_
  obtain ⟨F, hF, hdvd⟩ := F
  change _ ≤ kthMag F k
  set D := F.natDegree
  have hLD := le_natDegree_of_dvd hF hdvd
  by_contra hlt
  push_neg at hlt
  set I := ⨅ S : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k}, 1 / muR r S.1 L
  set T := (kthMag F k + I) / 2
  have hbT : kthMag F k < T := by linarith
  have hTI : T < I := by linarith
  have hT : 0 < T := lt_of_le_of_lt (kthMag_nonneg hk (by omega)) hbT
  have hcount : largeCount F T < k :=
    not_le.1 fun h => absurd ((le_largeCount_iff hk (by omega)).1 h) (not_le.2 hbT)
  set P := (Finset.range D).filter fun j => T ≤ ‖F.coeff j‖
  set W := P.image fun j => D - j
  have hWt : W ⊆ Finset.Icc 1 (D + k) := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hPc : P.card ≤ k - 1 := by
    have : largeCount F T = P.card := rfl
    omega
  obtain ⟨S, hWS, hSt, hSc⟩ := Finset.exists_subsuperset_card_eq hWt
    (Finset.card_image_le.trans hPc) (by rw [Nat.card_Icc]; omega)
  have hS0 : 0 ∉ S := fun h => by
    have := Finset.mem_Icc.1 (hSt h)
    omega
  have hle := inv_muR_le hr hF hdvd hS0 (by omega) hT fun j hj hjS => by
    refine not_lt.1 fun hbig => hjS (hWS (Finset.mem_image.2 ⟨j, ?_, rfl⟩))
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hbig.le⟩
  have hI : I ≤ 1 / muR r S L :=
    ciInf_le ⟨0, by
      rintro _ ⟨S', rfl⟩
      exact div_nonneg zero_le_one (muR_nonneg hr _ _)⟩
      (⟨S, hS0, by omega⟩ : {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k})
  linarith

end CoefficientMass
