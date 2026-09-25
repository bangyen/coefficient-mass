/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ExpSum
import CoefficientMass.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The Certificate with Excluded Positions

This module proves Lemma 3.1 of `coefficient-mass.tex` from the zero bound
and Theorem 2.2.  The zero bound makes the generalized Vandermonde system
invertible, so a certificate exists for any zero set; its dual identity
`∑_j f_j w_{D-j} = 0` holds because every node is a reciprocal root of `F`;
and the tail bound caps the certificate's weight on the positions outside `U`.

## Theorems

* `exists_certificate`.
* `sum_coeff_mul_expSum`.
* `nodeProduct_inv_rev`.
* `certificateWithExclusions_of_tailBound`.
-/

namespace CoefficientMass

/-- The zero bound makes the generalized Vandermonde system solvable: on `c`
distinct positive nodes there is a certificate for any zero set of `c - 1`
positive integers. -/
theorem exists_certificate (hzb : ZeroBound) {c : ℕ} (y : Fin c → ℝ)
    (hy : Function.Injective y) (hpos : ∀ i, 0 < y i) (Z : Finset ℕ) (h0 : 0 ∉ Z)
    (hcard : Z.card + 1 = c) : ∃ a, IsCertificate a y Z := by
  classical
  set S := insert 0 Z with hS
  have hSc : S.card = c := by rw [hS, Finset.card_insert_of_notMem h0, hcard]
  let M : (Fin c → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun a k => expSum a y k
      map_add' := fun a b => by
        funext k
        simp only [expSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun t a => by
        funext k
        simp only [expSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have hsub : ((S.image (Nat.cast : ℕ → ℝ) : Finset ℝ) : Set ℝ) ⊆
        {t : ℝ | ∑ i, a i * y i ^ t = 0} := by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
      have := congrFun ha ⟨k, hk⟩
      simp only [Set.mem_setOf_eq, Real.rpow_natCast]
      exact this
    have h1 := (Set.encard_le_encard hsub).trans (hzb c a y hy hpos hne)
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ Nat.cast_injective,
      hSc] at h1
    have : c ≤ c - 1 := by exact_mod_cast h1
    omega
  have hrank : Module.finrank ℝ (Fin c → ℝ) = Module.finrank ℝ (S → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hSc]
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
    (fun k => if k.val = 0 then 1 else 0)
  refine ⟨a, ?_, fun z hz => ?_⟩
  · have := congrFun ha ⟨0, Finset.mem_insert_self 0 Z⟩
    exact this
  · have := congrFun ha ⟨z, Finset.mem_insert_of_mem hz⟩
    exact this.trans (if_neg fun h : z = 0 => h0 (h ▸ hz))

/-- The dual identity: if every `1 / y_i` is a root of `F`, then
`∑_{j ≤ D} f_j w_{D-j} = 0` for every exponential sum `w` on the nodes `y`. -/
theorem sum_coeff_mul_expSum {c : ℕ} (a y : Fin c → ℝ) (hy : ∀ i, y i ≠ 0)
    (F : Polynomial ℝ) (hF : ∀ i, F.eval (y i)⁻¹ = 0) :
    ∑ j ∈ Finset.range (F.natDegree + 1), F.coeff j * expSum a y (F.natDegree - j) = 0 := by
  have hi : ∀ i, ∑ j ∈ Finset.range (F.natDegree + 1),
      F.coeff j * y i ^ (F.natDegree - j) = 0 := fun i => by
    have h := congrArg (· * y i ^ F.natDegree) (hF i)
    simp only [zero_mul, Polynomial.eval_eq_sum_range, Finset.sum_mul] at h
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h
    rw [pow_sub₀ _ (hy i) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), inv_pow]
    ring
  simp only [expSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_zero (a i), ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The certificate nodes `y_k = 1 / r_{L-1-k}` give
`nodeProduct y (L - 1 - u) = 1 / ∏_{i ≥ u} (r_i - 1)`. -/
theorem nodeProduct_inv_rev {L : ℕ} (r : Fin L → ℝ) (hr : ∀ i, 1 < r i) (u : ℕ)
    (hu : u < L) :
    nodeProduct (fun k => (r (Fin.rev k))⁻¹) (L - 1 - u) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin L => u ≤ i.val), (r i - 1))⁻¹ := by
  rw [nodeProduct, ← Finset.prod_inv_distrib]
  refine Finset.prod_nbij' Fin.rev Fin.rev (fun k hk => ?_) (fun i hi => ?_)
    (fun k _ => Fin.rev_rev k) (fun i _ => Fin.rev_rev i) (fun k _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hk ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢
    omega
  · have h := hr (Fin.rev k)
    have h0 : r (Fin.rev k) ≠ 0 := by positivity
    have h1 : r (Fin.rev k) - 1 ≠ 0 := by linarith
    field_simp

/-- Lemma 3.1 from the zero bound and Theorem 2.2. -/
theorem certificateWithExclusions_of_tailBound (hzb : ZeroBound) (htb : TailBound) :
    CertificateWithExclusions := by
  classical
  intro L r F U hmono hr hdvd hlead hU hUD
  set D := F.natDegree with hD
  set u := U.card with hu
  set ℓ := L - 1 - u with hℓ
  set T := ∏ i ∈ Finset.univ.filter (fun i : Fin L => u ≤ i.val), (r i - 1) with hT
  set y : Fin L → ℝ := fun k => (r (Fin.rev k))⁻¹ with hy
  have hr1 : ∀ i, 1 < r i := fun i => by linarith [hr i]
  have hypos : ∀ k, 0 < y k := fun k => inv_pos.2 (by linarith [hr (Fin.rev k)])
  have hymono : StrictMono y := fun k k' hkk' =>
    (inv_lt_inv₀ (by linarith [hr (Fin.rev k)]) (by linarith [hr (Fin.rev k')])).2
      (hmono (Fin.rev_lt_rev.2 hkk'))
  have hyhalf : ∀ k, y k ≤ 1 / 2 := fun k => by
    rw [one_div]
    exact inv_anti₀ two_pos (hr _)
  have hTpos : 0 < T := Finset.prod_pos fun i _ => by linarith [hr i]
  -- the zero set: the distances of `U` and a leading run of length `ℓ`
  set W := U.image (fun j => D - j) with hW
  have hZ0 : W ∪ Finset.Icc 1 ℓ ⊆ Finset.Icc 1 (D + L) := by
    intro d hd
    rcases Finset.mem_union.1 hd with hd | hd
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hd
      have := Finset.mem_range.1 (hUD hj)
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · have := Finset.mem_Icc.1 hd
      exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
  have hZ0card : (W ∪ Finset.Icc 1 ℓ).card ≤ L - 1 := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [Nat.card_Icc]
    have := Finset.card_image_le (s := U) (f := fun j => D - j)
    rw [← hW] at this
    omega
  obtain ⟨Z, hZ0Z, hZsub, hZcard⟩ := Finset.exists_subsuperset_card_eq hZ0 hZ0card
    (by rw [Nat.card_Icc]; omega)
  have h0 : 0 ∉ Z := fun h => by have := Finset.mem_Icc.1 (hZsub h); omega
  obtain ⟨a, ha⟩ := exists_certificate hzb y hymono.injective hypos Z h0 (by omega)
  obtain ⟨hsumm, htail⟩ := htb L a y Z ℓ hymono hypos hyhalf h0 hZcard
    (fun d hd => hZ0Z (Finset.mem_union_right _ hd)) ha
  rw [hy, nodeProduct_inv_rev r hr1 u hU, ← hT] at htail
  -- the dual identity, with the leading term split off
  have hev : ∀ i, F.eval (y i)⁻¹ = 0 := fun i => by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hy, inv_inv, hQ, Polynomial.eval_mul, rootProduct, Polynomial.eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ (Fin.rev i)), zero_mul]
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have hdual := sum_coeff_mul_expSum a y (fun i => (hypos i).ne') F hev
  rw [Finset.sum_range_succ, ← hD, Nat.sub_self, ha.1, mul_one] at hdual
  set S := (Finset.range D).filter (· ∉ U) with hS
  have hlead' : |F.coeff D| = 1 := by rw [← Real.norm_eq_abs]; exact hlead
  have h1 : 1 ≤ ∑ j ∈ S, |F.coeff j| * |expSum a y (D - j)| := by
    rw [← hlead', eq_neg_of_add_eq_zero_right hdual, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    have hfilt : ∑ j ∈ S, |F.coeff j * expSum a y (D - j)| =
        ∑ j ∈ Finset.range D, |F.coeff j * expSum a y (D - j)| :=
      Finset.sum_filter_of_ne fun j _ hne hj => hne (by
        rw [ha.2 _ (hZ0Z (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))), mul_zero,
          abs_zero])
    rw [← hfilt]
    exact Finset.sum_congr rfl fun j _ => abs_mul _ _
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨j, hjS, hjmax⟩ := S.exists_max_image (fun j => |F.coeff j|) hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hjS
  refine ⟨j, hjS.1, hjS.2, ?_⟩
  -- the weight of the certificate outside `U` is at most its tail
  have hweight : ∑ j ∈ S, |expSum a y (D - j)| ≤ T⁻¹ := by
    have hinj : Set.InjOn (fun j => D - 1 - j) S := fun j hj j' hj' h => by
      rw [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_range] at hj hj'
      simp only at h
      omega
    refine le_trans (le_of_eq ?_) ((hsumm.sum_le_tsum (S.image fun j => D - 1 - j)
      fun _ _ => abs_nonneg _).trans htail)
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hS, Finset.mem_filter, Finset.mem_range] at hj
    rw [show D - 1 - j + 1 = D - j by omega]
  have hbound : 1 ≤ |F.coeff j| * T⁻¹ := by
    refine h1.trans ((Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hjmax k hk) (abs_nonneg _)).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hweight (abs_nonneg _)
  rw [← div_eq_mul_inv, one_le_div₀ hTpos] at hbound
  rw [Real.norm_eq_abs]
  exact hbound

end CoefficientMass
