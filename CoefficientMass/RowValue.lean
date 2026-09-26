/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowCert

/-!
# The Row Values at a Root `r > 1`

This module proves Proposition 2.1(a) of `coefficient-mass-rows.tex`, the certificate lemma
for a row with `2` replaced by `r`.  For a monic multiple `F` of `(x - r)^L` and
real `q` with `deg q < L` and `q(0) = 1`, the dual identity `∑_j f_j q(D - j) r^{j - D} = 0`
gives `1 ≤ B Φ_r(q)` for every `B` bounding the `|f_j|`, `j < D`, with `q(D - j) ≠ 0`.
If `q` vanishes on the backward distances of `k - 1` largest nonleading magnitudes, then
`b_k(F) Φ_r(q) ≥ 1`.

## Definitions

* `rowPhi`.
* `RowValueCert`.

## Theorems

* `summable_rowPhi`.
* `sum_le_rowPhi`.
* `one_le_mul_rowPhi`.
* `rowValueCert`.
-/

open Polynomial

namespace CoefficientMass

/-- `Φ_r(q) = ∑_{s ≥ 1} |q(s)| r^{-s}`, indexed from `s = d + 1`. -/
noncomputable def rowPhi (r : ℝ) (q : ℝ[X]) : ℝ :=
  ∑' d : ℕ, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)

/-- Proposition 2.1(a) of `coefficient-mass-rows.tex`: let `r > 1`, let `F` be a monic
multiple of `(x - r)^L` of degree `D`, let `J ⊆ [0, D - 1]` carry `k - 1` largest nonleading
magnitudes, and let `q` be real with `deg q < L`, `q(0) = 1` and `q = 0` on the backward
distances `S = {D - j : j ∈ J}`.  Then `b_k(F) ≥ 1 / Φ_r(q)`; in particular
`b_k(F) ≥ 1 / Φ_r(Z)` for every finite `Z ⊇ S` with `|Z| ≤ L - 1`. -/
def RowValueCert : Prop :=
  ∀ (r : ℝ) (L k : ℕ) (F : ℝ[X]) (J : Finset ℕ), 1 < r → F.Monic → (X - C r) ^ L ∣ F →
    J ⊆ Finset.range F.natDegree → J.card + 1 = k →
    (∀ i ∈ J, ∀ j < F.natDegree, j ∉ J → ‖F.coeff j‖ ≤ ‖F.coeff i‖) →
    (∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 →
      (∀ j ∈ J, q.eval ((F.natDegree - j : ℕ) : ℝ) = 0) →
        k ≤ largeCount F (1 / rowPhi r q)) ∧
    ∀ Z : Finset ℕ, (∀ j ∈ J, F.natDegree - j ∈ Z) → Z.card + 1 ≤ L →
      k ≤ largeCount F (1 / rowPhi r (confPolyP Z))

theorem summable_rowPhi {r : ℝ} (hr : 1 < r) (p : ℝ[X]) :
    Summable fun d : ℕ => |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by
  have hr' : ‖(1 / r : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by linarith)]
    exact hr
  have hg : ∀ i, Summable fun d : ℕ =>
      |p.coeff i| * (((d + 1 : ℕ) : ℝ) ^ i * (1 / r) ^ (d + 1)) :=
    fun i => ((summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one i
      hr')).mul_left _
  refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    (summable_sum fun i (_ : i ∈ Finset.range (p.natDegree + 1)) => hg i)
  calc |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
      ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * ((d + 1 : ℕ) : ℝ) ^ i) *
          (1 / r) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right (abs_eval_le p (by positivity)) (by positivity)
    _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_le_rowPhi {r : ℝ} (hr : 1 < r) (p : ℝ[X]) (D : ℕ) :
    ∑ d ∈ Finset.range D, |p.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) ≤ rowPhi r p :=
  (summable_rowPhi hr p).sum_le_tsum _ fun _ _ => by positivity

/-- The dual identity at the root `r`: `1 ≤ B Φ_r(q)` whenever `B` bounds every `|f_j|`,
`j < D`, at which `q(D - j) ≠ 0`. -/
theorem one_le_mul_rowPhi {r : ℝ} (hr : 1 < r) {L : ℕ} {F q : ℝ[X]} (hF : F.Monic)
    (hdvd : (X - C r) ^ L ∣ F) (hq : q.degree < L) (hq0 : q.eval 0 = 1) {B : ℝ}
    (hB : ∀ j < F.natDegree, q.eval ((F.natDegree : ℝ) - j) ≠ 0 → ‖F.coeff j‖ ≤ B) :
    1 ≤ B * rowPhi r q := by
  set D := F.natDegree
  have hr0 : r ≠ 0 := by positivity
  have hrD : 0 < r ^ D := by positivity
  set q' := q.comp (C (D : ℝ) - X)
  have hq' : ∀ x : ℝ, q'.eval x = q.eval ((D : ℝ) - x) := fun x => by
    rw [eval_comp, eval_sub, eval_C, eval_X]
  have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  have hqL : q.natDegree < L := by
    rw [degree_eq_natDegree hqne] at hq
    exact_mod_cast hq
  have hq'deg : q'.degree < L := by
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (D : ℝ) - X).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le ((natDegree_C _).trans_le zero_le_one) natDegree_X_le)
    have := (natDegree_comp_le (p := q) (q := C (D : ℝ) - X)).trans
      (Nat.mul_le_mul_left q.natDegree h1)
    exact_mod_cast (show q'.natDegree < L by omega)
  obtain ⟨G, hG⟩ := hdvd
  have hFG : G * (X - C r) ^ L = F := by rw [hG, mul_comm]
  have hsum0 := sum_coeff_mul_eval_eq_zero hr0 L G q' (D + 1) hq'deg (by rw [hFG]; omega)
  rw [hFG, Finset.sum_range_succ, hq', sub_self, hq0,
    show F.coeff D = 1 from hF.coeff_natDegree] at hsum0
  have hle : r ^ D ≤ B * ∑ j ∈ Finset.range D, |q.eval ((D : ℝ) - j)| * r ^ j := by
    calc r ^ D = |∑ j ∈ Finset.range D, F.coeff j * q'.eval (j : ℝ) * r ^ j| := by
          rw [show ∑ j ∈ Finset.range D, F.coeff j * q'.eval (j : ℝ) * r ^ j = -r ^ D by
            linarith, abs_neg, abs_of_pos hrD]
      _ ≤ ∑ j ∈ Finset.range D, ‖F.coeff j‖ * |q.eval ((D : ℝ) - j)| * r ^ j := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r ^ j), Real.norm_eq_abs,
            hq']
      _ ≤ ∑ j ∈ Finset.range D, B * |q.eval ((D : ℝ) - j)| * r ^ j := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (by positivity)
          by_cases h : q.eval ((D : ℝ) - j) = 0
          · rw [h, abs_zero, mul_zero, mul_zero]
          · exact mul_le_mul_of_nonneg_right (hB j (Finset.mem_range.1 hj) h) (abs_nonneg _)
      _ = B * ∑ j ∈ Finset.range D, |q.eval ((D : ℝ) - j)| * r ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [sum_reflect hr0] at hle
  set P := ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
  have h1 : 1 ≤ B * P := by
    have : r ^ D * 1 ≤ r ^ D * (B * P) := by linarith
    exact le_of_mul_le_mul_left this hrD
  rcases le_or_gt 0 B with hB0 | hB0
  · exact h1.trans (mul_le_mul_of_nonneg_left (sum_le_rowPhi hr q D) hB0)
  · nlinarith

theorem rowValueCert : RowValueCert := by
  classical
  intro r L k F J hr hF hdvd hJ hJc hdom
  set D := F.natDegree
  have main : ∀ q : ℝ[X], q.degree < L → q.eval 0 = 1 →
      (∀ j ∈ J, q.eval ((D - j : ℕ) : ℝ) = 0) → k ≤ largeCount F (1 / rowPhi r q) := by
    intro q hq hq0 hqJ
    by_contra hlt
    push_neg at hlt
    set T := 1 / rowPhi r q
    set O := (Finset.range D).filter fun j => j ∉ J
    -- every position off `J` is below `T`
    have hsmall : ∀ j ∈ O, ‖F.coeff j‖ < T := by
      intro j hj
      obtain ⟨hjD, hjJ⟩ := Finset.mem_filter.1 hj
      by_contra hbig
      push_neg at hbig
      have hsub : insert j J ⊆ (Finset.range D).filter fun i => T ≤ ‖F.coeff i‖ := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Finset.mem_filter.2 ⟨hjD, hbig⟩
        · exact Finset.mem_filter.2 ⟨hJ hi, hbig.trans (hdom i hi j (Finset.mem_range.1 hjD) hjJ)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hjJ] at this
      have hcount : largeCount F T = ((Finset.range D).filter fun i => T ≤ ‖F.coeff i‖).card :=
        rfl
      rw [hcount] at hlt
      omega
    obtain ⟨B, hBT, hB⟩ : ∃ B < T, ∀ j ∈ O, ‖F.coeff j‖ ≤ B := by
      rcases O.eq_empty_or_nonempty with hO | hO
      · refine ⟨T - 1, by linarith, fun j hj => ?_⟩
        rw [hO] at hj
        exact absurd hj (Finset.notMem_empty j)
      · obtain ⟨j₀, hj₀, hmax⟩ := O.exists_max_image (fun j => ‖F.coeff j‖) hO
        exact ⟨_, hsmall j₀ hj₀, hmax⟩
    have hle := one_le_mul_rowPhi hr hF hdvd hq hq0 (B := B) fun j hj hne => by
      refine hB j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, fun hjJ => hne ?_⟩)
      rw [← hqJ j hjJ, Nat.cast_sub hj.le]
    have hΦ : 0 ≤ rowPhi r q := tsum_nonneg fun _ => by positivity
    rcases hΦ.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hle
      linarith
    · have : B * rowPhi r q < 1 := by
        calc B * rowPhi r q < T * rowPhi r q := mul_lt_mul_of_pos_right hBT h0
          _ = 1 := by rw [one_div, inv_mul_cancel₀ h0.ne']
      linarith
  refine ⟨main, fun Z hJZ hZc => main _ ?_ ?_ fun j hj => ?_⟩
  · refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast (natDegree_confPolyP Z).trans_lt (by omega)
  · rw [confPolyP, eval_prod]
    exact Finset.prod_eq_one fun z _ => by rw [eval_add, eval_mul, eval_C, eval_C, eval_X]; ring
  · have := Finset.mem_range.1 (hJ hj)
    exact confPolyP_eval_mem (hJZ j hj) (by omega)

end CoefficientMass
