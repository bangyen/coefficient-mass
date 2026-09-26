/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.PrefixPush
import CoefficientMass.RowPrefixRows

/-!
# One Polynomial for All Exempted Sets

This module proves Theorem 6.2 of `coefficient-mass-rows.tex`.  For `p ∈ Q_n`
(`deg p ≤ n - 1`, `p(0) = 1`) and an exempted set `S` with `|S| = k - 1`, the polynomial
`r_S p` is admissible for `μ_r(S, L)`, and Lemma 6.1 bounds its sum by
`max_{i ≤ k} A_i(p)`.  So `b_k(F) ≥ 1/max_{i ≤ k} A_i(p)`, and with
`Λ_k(n) = inf_p max_{i ≤ k} A_i(p)`, `1/Ω_k(n) ≤ 1/Λ_k(n) ≤ V_r(L, k) ≤ min_i 1/ν_i(n)`.

## Definitions

* `maxA`.
* `lambdaR`.
* `OnePoly`.

## Theorems

* `prefA_nonneg`.
* `le_maxA`.
* `maxA_nonneg`.
* `muR_le_rowPhi_mul`.
* `muR_le_maxA`.
* `nuR_le_prefA`.
* `nuR_pos`.
* `maxA_le_omega`.
* `onePoly`.
-/

open Polynomial

namespace CoefficientMass

/-- `max_{1 ≤ i ≤ k} A_i(p)` (and `0` for `k = 0`). -/
noncomputable def maxA (r : ℝ) (k : ℕ) (p : ℝ[X]) : ℝ :=
  (Finset.Icc 1 k).fold max 0 fun i => prefA r i p

/-- `Λ_k(n) = inf_{p ∈ Q_n} max_{i ≤ k} A_i(p)`. -/
noncomputable def lambdaR (r : ℝ) (k n : ℕ) : ℝ :=
  ⨅ p : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1}, maxA r k p.1

/-- Theorem 6.2 of `coefficient-mass-rows.tex`: for `r > 1`, `1 ≤ k ≤ L`, `n = L - k + 1` and
`p ∈ Q_n`, every monic multiple `F` of `(x - r)^L` has `b_k(F) ≥ 1/max_{i ≤ k} A_i(p)`; hence
`1/Ω_k(n) ≤ 1/Λ_k(n) ≤ V_r(L, k) ≤ min_{i ≤ k} 1/ν_i(n)`. -/
def OnePoly : Prop :=
  ∀ r : ℝ, 1 < r → ∀ L k : ℕ, 1 ≤ k → k ≤ L →
    (∀ p : ℝ[X], p.degree < ↑(L - k + 1) → p.eval 0 = 1 → ∀ F : ℝ[X], F.Monic →
      (X - C r) ^ L ∣ F → 1 / maxA r k p ≤ kthMag F k) ∧
    1 / omegaR r k (L - k + 1) ≤ 1 / lambdaR r k (L - k + 1) ∧
    1 / lambdaR r k (L - k + 1) ≤ rowValue r L k ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k → rowValue r L k ≤ 1 / nuR r i (L - k + 1)

theorem prefA_nonneg {r : ℝ} (hr : 1 < r) (i : ℕ) (p : ℝ[X]) : 0 ≤ prefA r i p :=
  tsum_nonneg fun s => mul_nonneg (prefixWeight_le hr i s).1 (abs_nonneg _)

theorem le_maxA {r : ℝ} {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (p : ℝ[X]) :
    prefA r i p ≤ maxA r k p :=
  (Finset.le_fold_max _).2 (Or.inr ⟨i, Finset.mem_Icc.2 ⟨hi, hik⟩, le_rfl⟩)

theorem maxA_nonneg (r : ℝ) (k : ℕ) (p : ℝ[X]) : 0 ≤ maxA r k p :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

/-- `μ_r(S, L) ≤ Φ_r(r_S p)` for `deg p < L - |S|` and `p(0) = 1`. -/
theorem muR_le_rowPhi_mul {r : ℝ} (hr : 1 < r) {S : Finset ℕ} (h0 : 0 ∉ S) {L : ℕ}
    {p : ℝ[X]} (hp : p.degree < ↑(L - S.card)) (hp0 : p.eval 0 = 1) (hSL : S.card < L) :
    muR r S L ≤ rowPhi r (confPolyP S * p) := by
  have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
  have hpn : p.natDegree < L - S.card := by
    rw [degree_eq_natDegree hpne] at hp
    exact_mod_cast hp
  have hadm := confPolyP_admissible h0 hSL
  have hq : (confPolyP S * p).degree < L := by
    have : (confPolyP S * p).natDegree ≤ S.card + p.natDegree :=
      (natDegree_mul_le (p := confPolyP S) (q := p)).trans
        (add_le_add (natDegree_confPolyP S) le_rfl)
    exact degree_le_natDegree.trans_lt
      (by exact_mod_cast (show (confPolyP S * p).natDegree < L by omega))
  have hq0 : (confPolyP S * p).eval 0 = 1 := by rw [eval_mul, hadm.2.1, hp0, one_mul]
  have hqS : ∀ s ∈ S, (confPolyP S * p).eval (s : ℝ) = 0 := fun s hs => by
    rw [eval_mul, hadm.2.2 s hs, zero_mul]
  exact ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by
        have : 0 < 1 / r := by positivity
        positivity⟩
    (⟨_, hq, hq0, hqS⟩ : {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})

/-- `μ_r(S, L) ≤ max_{i ≤ k} A_i(p)` for `|S| = k - 1` and `p ∈ Q_{L - k + 1}`. -/
theorem muR_le_maxA {r : ℝ} (hr : 1 < r) {L k : ℕ} (hkL : k ≤ L) {S : Finset ℕ} (h0 : 0 ∉ S)
    (hSk : S.card + 1 = k) {p : ℝ[X]} (hp : p.degree < ↑(L - k + 1)) (hp0 : p.eval 0 = 1) :
    muR r S L ≤ maxA r k p := by
  obtain ⟨i, hi1, hik, hi⟩ := prefixPush hr p h0
  exact (muR_le_rowPhi_mul hr h0 (by rwa [show L - S.card = L - k + 1 by omega]) hp0
    (by omega)).trans (hi.trans (le_maxA hi1 (by omega) p))

/-- `ν_i(n) ≤ A_i(p)` for `p ∈ Q_n`. -/
theorem nuR_le_prefA {r : ℝ} (hr : 1 < r) (i : ℕ) {n : ℕ} {p : ℝ[X]} (hp : p.degree < n)
    (hp0 : p.eval 0 = 1) : nuR r i n ≤ prefA r i p :=
  ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun s => mul_nonneg (prefixWeight_le hr i s).1 (abs_nonneg _)⟩
    (⟨p, hp, hp0⟩ : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})

theorem nuR_pos {r : ℝ} (hr : 1 < r) {i n : ℕ} (hi : 1 ≤ i) (hn : 1 ≤ n) : 0 < nuR r i n := by
  rw [← muR_prefix hr hi hn]
  exact muR_pos hr (fun h => by have := (Finset.mem_Icc.1 h).1; omega)
    (by rw [Nat.card_Icc]; omega)

/-- `max_{i ≤ k} A_i(p) ≤ ∑_s W_k(s) r^{-s} |p(s)|` for `deg p < n`. -/
theorem maxA_le_omega {r : ℝ} (hr : 1 < r) (k : ℕ) {n : ℕ} {p : ℝ[X]} (hp : p.degree < n)
    (hp0 : p.eval 0 = 1) : maxA r k p ≤ ∑' s : ℕ, omegaWeight r k s * |p.eval (s : ℝ)| := by
  have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
  have hpn : p.natDegree < n := by
    rw [degree_eq_natDegree hpne] at hp
    exact_mod_cast hp
  have hΩ := summable_weighted (fun s => (omegaWeight_le hr k s).1)
    (summable_weight_pow hr (omegaWeight_le hr k) (n - 1)) _
    fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  refine (Finset.fold_max_le _).2 ⟨tsum_nonneg fun s =>
    mul_nonneg (omegaWeight_le hr k s).1 (abs_nonneg _), fun i hi => ?_⟩
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  have hA := summable_weighted (fun s => (prefixWeight_le hr i s).1)
    (summable_weight_pow hr (prefixWeight_le hr i) (n - 1)) _
    fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
  refine Summable.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) hA hΩ
  unfold prefixWeight omegaWeight
  split_ifs with hs
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast choose_le_wK (by omega)
  · exact le_rfl

theorem onePoly : OnePoly := by
  intro r hr L k hk hkL
  set n := L - k + 1
  have hn : 1 ≤ n := by omega
  haveI hQ : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k} :=
    ⟨⟨Finset.Icc 1 (k - 1), fun h => by have := (Finset.mem_Icc.1 h).1; omega,
      by rw [Nat.card_Icc]; omega⟩⟩
  have hbdd : BddBelow (Set.range fun p : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} =>
      maxA r k p.1) := ⟨0, by rintro _ ⟨p, rfl⟩; exact maxA_nonneg r k p.1⟩
  -- `ν_k(n) ≤ Λ_k(n)`, so `Λ_k(n) > 0`
  have hΛ : 0 < lambdaR r k n := (nuR_pos hr hk hn).trans_le (le_ciInf fun p =>
    (nuR_le_prefA hr k p.2.1 p.2.2).trans (le_maxA hk le_rfl p.1))
  -- `μ_r(S, L) ≤ Λ_k(n)` for every exempted set
  have hμΛ : ∀ S : Finset ℕ, 0 ∉ S → S.card + 1 = k → muR r S L ≤ lambdaR r k n :=
    fun S h0 hSk => le_ciInf fun p => muR_le_maxA hr hkL h0 hSk p.2.1 p.2.2
  have hV : 1 / lambdaR r k n ≤ rowValue r L k := by
    rw [(rowValueDual r hr).1 L k hk hkL]
    exact le_ciInf fun S => one_div_le_one_div_of_le (muR_pos hr S.2.1 (by have := S.2.2; omega))
      (hμΛ S.1 S.2.1 S.2.2)
  refine ⟨fun p hp hp0 F hF hdvd => ?_, one_div_le_one_div_of_le hΛ (le_ciInf fun p =>
    (ciInf_le hbdd p).trans (maxA_le_omega hr k p.2.1 p.2.2)), hV,
    (prefixRows r hr L k hk hkL).2.2⟩
  have hVp : 1 / maxA r k p ≤ rowValue r L k := by
    rw [(rowValueDual r hr).1 L k hk hkL]
    exact le_ciInf fun S => one_div_le_one_div_of_le (muR_pos hr S.2.1 (by have := S.2.2; omega))
      (muR_le_maxA hr hkL S.2.1 S.2.2 hp hp0)
  refine hVp.trans (ciInf_le ⟨0, ?_⟩ (⟨F, hF, hdvd⟩ : {F : ℝ[X] // F.Monic ∧ (X - C r) ^ L ∣ F}))
  rintro _ ⟨G, rfl⟩
  exact kthMag_nonneg hk (hkL.trans (le_natDegree_of_dvd G.2.1 G.2.2))

end CoefficientMass
