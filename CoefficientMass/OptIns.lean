/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.OptInsCore

/-!
# Inserting at a Gap of a Minimizer

This module proves Lemma 5.2 of `coefficient-mass-rows.tex` for finite truncations `D`.  If
`r_W` attains `μ_{r,D}(T, |W| + 1)` and `c ∉ W` lies above `T`, then `P + ε H`, with
`H = P - Q - κ s P`, is admissible for every `ε`, which is the optimality `opt_core` needs.

## Definitions

* `insDir`.
* `OptIns`.
* `OptInsMax`.

## Theorems

* `kappa_pos`.
* `eval_insDir`.
* `degree_insDir_lt`.
* `optIns`.
* `optInsMax`.
-/

open Polynomial

namespace CoefficientMass

/-- `P + ε (P - Q - κ s P)` with `P = r_W`, `Q = r_{ins(W, c)}`. -/
noncomputable def insDir (W : Finset ℕ) (c : ℕ) (ε : ℝ) : ℝ[X] :=
  confPolyP W + C ε * (confPolyP W - confPolyP (ins W c) - C (kappa W c) * X * confPolyP W)

/-- Lemma 5.2 of `coefficient-mass-rows.tex` (finite `D`): with `φ = Φ_{r,D}(r_W)` equal to
`μ_{r,D}(T, |W| + 1)`, `T ⊆ W`, `1 ≤ c ∉ W`, `c > max T` and `Q = r_{ins(W, c)}`,
`(r - 1) Φ_{r,D}(Q) ≤ φ + (r - 2) Φ_{r,D}^{<c}(Q)` and
`Φ_{r,D}^{<c}(Q) ≤ Φ_{r,D}^{<c}(r_W)`. -/
def OptIns : Prop :=
  ∀ (r : ℝ), 1 < r → ∀ (D : ℕ) (T W : Finset ℕ) (c : ℕ), 0 ∉ W → T ⊆ W → 1 ≤ c → c ∉ W →
    (∀ t ∈ T, t < c) → phiD r D (confPolyP W) = muRD r D T (W.card + 1) →
    (r - 1) * phiD r D (confPolyP (ins W c)) ≤
        phiD r D (confPolyP W) + (r - 2) * phiLt r D c (confPolyP (ins W c)) ∧
      phiLt r D c (confPolyP (ins W c)) ≤ phiLt r D c (confPolyP W)

/-- Lemma 5.2 of `coefficient-mass-rows.tex`, the consequence: under the hypotheses of `OptIns`,
`Φ_{r,D}(Q) ≤ max(1, 1/(r - 1)) φ`, and `Φ_{r,D}(Q) ≤ φ` for `r ≥ 2`. -/
def OptInsMax : Prop :=
  ∀ (r : ℝ), 1 < r → ∀ (D : ℕ) (T W : Finset ℕ) (c : ℕ), 0 ∉ W → T ⊆ W → 1 ≤ c → c ∉ W →
    (∀ t ∈ T, t < c) → phiD r D (confPolyP W) = muRD r D T (W.card + 1) →
    phiD r D (confPolyP (ins W c)) ≤ max 1 (1 / (r - 1)) * phiD r D (confPolyP W) ∧
      (2 ≤ r → phiD r D (confPolyP (ins W c)) ≤ phiD r D (confPolyP W))

theorem kappa_pos (W : Finset ℕ) {c : ℕ} (hc1 : 1 ≤ c) : 0 < kappa W c := by
  rw [kappa]
  exact one_div_pos.2 (mul_pos (by exact_mod_cast hc1) (Finset.prod_pos fun w _ => by positivity))

theorem eval_insDir (W : Finset ℕ) (c : ℕ) (ε y : ℝ) :
    (insDir W c ε).eval y = (1 + ε - ε * kappa W c * y) * (confPolyP W).eval y -
      ε * (confPolyP (ins W c)).eval y := by
  simp only [insDir, eval_add, eval_mul, eval_C, eval_sub, eval_X]
  ring

theorem degree_insDir_lt {W : Finset ℕ} {c : ℕ} (h0 : 0 ∉ W) (hc : c ∉ W) (hc1 : 1 ≤ c)
    (ε : ℝ) : (insDir W c ε).degree < ((W.card + 1 : ℕ) : WithBot ℕ) := by
  have hP : (confPolyP W).degree < ((W.card + 1 : ℕ) : WithBot ℕ) :=
    (degree_le_of_natDegree_le (natDegree_confPolyP W)).trans_lt
      (by exact_mod_cast Nat.lt_succ_self _)
  have hH := degree_ins_dir_lt h0 hc hc1
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  have hm' : ((W.card + 1 : ℕ) : WithBot ℕ) ≤ m := by exact_mod_cast hm
  rw [insDir, coeff_add, coeff_C_mul, coeff_eq_zero_of_degree_lt (hP.trans_le hm'),
    coeff_eq_zero_of_degree_lt (hH.trans_le hm'), mul_zero, add_zero]

theorem optIns : OptIns := by
  intro r hr D T W c h0 hTW hc1 hc hTc hopt
  have hQc : (confPolyP (ins W c)).eval (c : ℝ) = 0 :=
    confPolyP_eval_mem (mem_ins_self W c) (by omega)
  have hP0 := (confPolyP_admissible (L := W.card + 1) h0 (Nat.lt_succ_self _)).2.1
  have hQ0 : (confPolyP (ins W c)).eval 0 = 1 := by
    rw [eval_confPolyP]
    simp only [zero_div, sub_zero, Finset.prod_const_one]
  have hdir : ∀ ε : ℝ, phiD r D (confPolyP W) ≤ ∑ s ∈ Finset.Icc 1 D,
      |(1 + ε - ε * kappa W c * s) * (confPolyP W).eval (s : ℝ) -
        ε * (confPolyP (ins W c)).eval (s : ℝ)| * (1 / r) ^ s := fun ε => by
    have hq0 : (insDir W c ε).eval 0 = 1 := by
      rw [eval_insDir, hP0, hQ0]
      ring
    have hqT : ∀ t ∈ T, (insDir W c ε).eval (t : ℝ) = 0 := fun t ht => by
      have htW := hTW ht
      have ht0 : t ≠ 0 := fun h => h0 (h ▸ htW)
      have htQ : t ∈ ins W c := Finset.mem_union_left _ (Finset.mem_filter.2 ⟨htW, hTc t ht⟩)
      rw [eval_insDir, confPolyP_eval_mem htW ht0, confPolyP_eval_mem htQ ht0]
      ring
    have hphi : phiD r D (insDir W c ε) = ∑ s ∈ Finset.Icc 1 D,
        |(1 + ε - ε * kappa W c * s) * (confPolyP W).eval (s : ℝ) -
          ε * (confPolyP (ins W c)).eval (s : ℝ)| * (1 / r) ^ s := by
      rw [phiD]
      exact Finset.sum_congr rfl fun s _ => by rw [eval_insDir]
    rw [hopt]
    refine (ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact Finset.sum_nonneg fun _ _ => by positivity⟩
      (⟨insDir W c ε, degree_insDir_lt h0 hc hc1 ε, hq0, hqT⟩ :
        {q : ℝ[X] // q.degree < ((W.card + 1 : ℕ) : WithBot ℕ) ∧ q.eval 0 = 1 ∧
          ∀ s ∈ T, q.eval (s : ℝ) = 0})).trans_eq hphi
  refine ⟨opt_core (p := fun s => (confPolyP W).eval (s : ℝ))
    (q := fun s => (confPolyP (ins W c)).eval (s : ℝ)) hr (kappa_pos W hc1) hc1
    (fun s hs hsc => ⟨ins_sign_below h0 hc hsc, abs_ins_le_below hc hs hsc⟩)
    (fun s hs => hs.eq_or_lt.elim (fun h => by subst h; exact (mul_eq_zero_of_right _ hQc).le)
      fun h => ins_sign_above h0 hc hc1 h) hQc
    (fun u hu => abs_ins_shift h0 hc hc1 hu) hdir, ?_⟩
  refine Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_right ?_ (by positivity)
  obtain ⟨hsI, hsc⟩ := Finset.mem_filter.1 hs
  exact abs_ins_le_below hc (Finset.mem_Icc.1 hsI).1 hsc

theorem optInsMax : OptInsMax := by
  intro r hr D T W c h0 hTW hc1 hc hTc hopt
  obtain ⟨h1, h2⟩ := optIns r hr D T W c h0 hTW hc1 hc hTc hopt
  have hsplit := phiD_split r D c (confPolyP W)
  have hge : 0 ≤ phiGe r D c (confPolyP W) := Finset.sum_nonneg fun _ _ => by positivity
  have hlt : 0 ≤ phiLt r D c (confPolyP (ins W c)) := Finset.sum_nonneg fun _ _ => by positivity
  have hφ : 0 ≤ phiD r D (confPolyP W) := Finset.sum_nonneg fun _ _ => by positivity
  have hr1 : 0 < r - 1 := by linarith
  have htwo : 2 ≤ r → phiD r D (confPolyP (ins W c)) ≤ phiD r D (confPolyP W) := fun h2r => by
    have hPlt : phiLt r D c (confPolyP W) ≤ phiD r D (confPolyP W) := by linarith
    have := mul_le_mul_of_nonneg_left (h2.trans hPlt) (by linarith : (0 : ℝ) ≤ r - 2)
    refine le_of_mul_le_mul_left ?_ hr1
    linarith
  refine ⟨?_, htwo⟩
  rcases le_or_gt 2 r with h2r | h2r
  · exact (htwo h2r).trans (le_mul_of_one_le_left hφ (le_max_left _ _))
  · have hneg : (r - 2) * phiLt r D c (confPolyP (ins W c)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlt
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hφ)
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hr1]
    linarith

end CoefficientMass
