/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# The Operators `T_z`

This module proves the zero count of Proposition 4.2 of `coefficient-mass.tex`.  For
`z ≥ 1`, `T_z h = h - (x / z) h'` multiplies the coefficient at `x^d` by `1 - d / z`, and
`T_z h = -(x^{z+1} / z) (x^{-z} h)'`.  A root of `h` of multiplicity `m` is a root of
`T_z h` of multiplicity at least `m - 1`, and Rolle's theorem for `x^{-z} h` puts a root of
`T_z h` strictly between two consecutive roots of `h` in `(0, 1/2]`; so `T_z h` keeps all
but one of the roots of `h` in `(0, 1/2]`, counted with multiplicity.

## Definitions

* `tOp`.
* `tOps`.
* `rootsIn`.

## Theorems

* `coeff_X_mul_derivative`.
* `coeff_tOp`.
* `eval_tOp`.
* `eval_tOp_zero`.
* `sum_count_le_card`.
* `card_rootsIn_le`.
* `coeff_tOps`.
* `eval_zero_tOps`.
* `card_rootsIn_tOps`.
-/

open Polynomial

namespace CoefficientMass

/-- `T_z h = h - (x / z) h'`. -/
noncomputable def tOp (z : ℕ) (h : ℝ[X]) : ℝ[X] :=
  h - C ((z : ℝ)⁻¹) * (X * derivative h)

/-- `T_{z_1} ⋯ T_{z_n} h`. -/
noncomputable def tOps : List ℕ → ℝ[X] → ℝ[X]
  | [], h => h
  | z :: l, h => tOp z (tOps l h)

/-- The roots of `h` in `(0, 1/2]`, with multiplicity. -/
noncomputable def rootsIn (h : ℝ[X]) : Multiset ℝ :=
  h.roots.filter fun x => 0 < x ∧ x ≤ 1 / 2

theorem coeff_X_mul_derivative (h : ℝ[X]) (d : ℕ) :
    (X * derivative h).coeff d = d * h.coeff d := by
  rcases d with _ | n
  · rw [coeff_X_mul_zero, Nat.cast_zero, zero_mul]
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem coeff_tOp (z : ℕ) (h : ℝ[X]) (d : ℕ) :
    (tOp z h).coeff d = (1 - (d : ℝ) / z) * h.coeff d := by
  rw [tOp, coeff_sub, coeff_C_mul, coeff_X_mul_derivative]
  ring

theorem eval_tOp (z : ℕ) (h : ℝ[X]) (c : ℝ) :
    (tOp z h).eval c = h.eval c - (z : ℝ)⁻¹ * (c * (derivative h).eval c) := by
  rw [tOp, eval_sub, eval_mul, eval_C, eval_mul, eval_X]

theorem eval_tOp_zero (z : ℕ) (h : ℝ[X]) : (tOp z h).eval 0 = h.eval 0 := by
  rw [eval_tOp, zero_mul, mul_zero, sub_zero]

theorem sum_count_le_card (A : Finset ℝ) (m : Multiset ℝ) :
    ∑ x ∈ A, m.count x ≤ Multiset.card m := by
  calc ∑ x ∈ A, m.count x ≤ ∑ x ∈ A ∪ m.toFinset, m.count x :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ x ∈ m.toFinset, m.count x :=
        (Finset.sum_subset Finset.subset_union_right fun x _ hx =>
          Multiset.count_eq_zero.2 fun h => hx (Multiset.mem_toFinset.2 h)).symm
    _ = Multiset.card m := Multiset.toFinset_sum_count_eq m

/-- `T_z h` keeps all but one of the roots of `h` in `(0, 1/2]`. -/
theorem card_rootsIn_le {z : ℕ} (hz : 1 ≤ z) {h : ℝ[X]} (h0 : h.eval 0 ≠ 0) :
    Multiset.card (rootsIn h) ≤ Multiset.card (rootsIn (tOp z h)) + 1 := by
  have hh : h ≠ 0 := fun e => h0 (by rw [e, eval_zero])
  have hq : tOp z h ≠ 0 := fun e => h0 (by rw [← eval_tOp_zero z h, e, eval_zero])
  have hz' : (z : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set q := tOp z h with hqdef
  set s := (rootsIn h).toFinset
  set t := (rootsIn q).toFinset
  have hmem : ∀ {p : ℝ[X]} {x : ℝ},
      x ∈ (rootsIn p).toFinset ↔ x ∈ p.roots ∧ (0 < x ∧ x ≤ 1 / 2) := by
    intro p x
    rw [Multiset.mem_toFinset, rootsIn, Multiset.mem_filter]
  have hcount : ∀ (p : ℝ[X]) (x : ℝ), (0 < x ∧ x ≤ 1 / 2) →
      (rootsIn p).count x = p.rootMultiplicity x := fun p x hx => by
    rw [rootsIn, Multiset.count_filter_of_pos hx, count_roots]
  have hmult : ∀ x, h.rootMultiplicity x - 1 ≤ q.rootMultiplicity x := fun x => by
    rw [le_rootMultiplicity_iff hq]
    have h1 : (X - C x) ^ (h.rootMultiplicity x - 1) ∣ h :=
      (pow_dvd_pow _ (Nat.sub_le _ 1)).trans (pow_rootMultiplicity_dvd h x)
    have h2 : (X - C x) ^ (h.rootMultiplicity x - 1) ∣ derivative h :=
      (pow_dvd_pow _ (rootMultiplicity_sub_one_le_derivative_rootMultiplicity h x)).trans
        (pow_rootMultiplicity_dvd _ x)
    exact dvd_sub h1 (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2 X) _)
  have hint : s.card ≤ (t \ s).card + 1 := by
    refine Finset.card_le_diff_of_interleaved fun x hx y hy hxy _ => ?_
    rw [hmem] at hx hy
    have hxh : h.eval x = 0 := (mem_roots hh).1 hx.1
    have hyh : h.eval y = 0 := (mem_roots hh).1 hy.1
    have hx0 := hx.2.1
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hxy
      (f := fun u => h.eval u / u ^ z)
      (f' := fun u => ((derivative h).eval u * u ^ z - h.eval u * (z * u ^ (z - 1))) /
        (u ^ z) ^ 2)
      (h.continuous.continuousOn.div (continuousOn_pow z) fun u hu =>
        pow_ne_zero z (by linarith [hu.1] : (0 : ℝ) < u).ne')
      (by simp only [hxh, hyh, zero_div])
      fun u hu => (h.hasDerivAt u).div (hasDerivAt_pow z u)
        (pow_ne_zero z (by linarith [hu.1] : (0 : ℝ) < u).ne')
    have hcpos : 0 < c := by linarith [hc.1]
    have hcz : c ^ (z - 1) ≠ 0 := pow_ne_zero _ hcpos.ne'
    have hc0' : (derivative h).eval c * c ^ z - h.eval c * (z * c ^ (z - 1)) = 0 :=
      (div_eq_zero_iff.1 hc0).resolve_right (pow_ne_zero 2 (pow_ne_zero z hcpos.ne'))
    have e : c ^ z = c * c ^ (z - 1) := by rw [← pow_succ', Nat.sub_add_cancel hz]
    rw [e] at hc0'
    have k : c ^ (z - 1) * ((z : ℝ) * q.eval c) = 0 := by
      rw [hqdef, eval_tOp, mul_sub, ← mul_assoc (z : ℝ) (z : ℝ)⁻¹, mul_inv_cancel₀ hz', one_mul]
      linear_combination (-1 : ℝ) * hc0'
    have hqc : q.eval c = 0 := ((mul_eq_zero.1 ((mul_eq_zero.1 k).resolve_left hcz)).resolve_left hz')
    exact ⟨c, hmem.2 ⟨(mem_roots hq).2 hqc, hcpos, by linarith [hc.2, hy.2.2]⟩, hc.1, hc.2⟩
  calc Multiset.card (rootsIn h) = ∑ x ∈ s, (rootsIn h).count x :=
        (Multiset.toFinset_sum_count_eq _).symm
    _ ≤ ∑ x ∈ s, ((rootsIn q).count x + 1) := Finset.sum_le_sum fun x hx => by
        have hx' := (hmem.1 hx).2
        rw [hcount h x hx', hcount q x hx']
        have := hmult x
        omega
    _ = ∑ x ∈ s, (rootsIn q).count x + s.card := by
        rw [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    _ ≤ ∑ x ∈ s, (rootsIn q).count x + (∑ x ∈ t \ s, (rootsIn q).count x + 1) := by
        refine Nat.add_le_add_left (hint.trans (Nat.add_le_add_right ?_ 1)) _
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun x hx =>
          Multiset.count_pos.2 (Multiset.mem_toFinset.1 (Finset.mem_sdiff.1 hx).1)
    _ = ∑ x ∈ s ∪ (t \ s), (rootsIn q).count x + 1 := by
        rw [Finset.sum_union Finset.disjoint_sdiff, add_assoc]
    _ ≤ Multiset.card (rootsIn q) + 1 := Nat.add_le_add_right (sum_count_le_card _ _) 1

theorem coeff_tOps (l : List ℕ) (h : ℝ[X]) (d : ℕ) :
    (tOps l h).coeff d = h.coeff d * (l.map fun z => 1 - (d : ℝ) / z).prod := by
  induction l with
  | nil => rw [tOps, List.map_nil, List.prod_nil, mul_one]
  | cons z l ih =>
    rw [tOps, coeff_tOp, ih, List.map_cons, List.prod_cons]
    ring

theorem eval_zero_tOps (l : List ℕ) (h : ℝ[X]) : (tOps l h).eval 0 = h.eval 0 := by
  induction l with
  | nil => rw [tOps]
  | cons z l ih => rw [tOps, eval_tOp_zero, ih]

/-- `T_{z_1} ⋯ T_{z_n} h` keeps all but `n` of the roots of `h` in `(0, 1/2]`. -/
theorem card_rootsIn_tOps (h : ℝ[X]) (h0 : h.eval 0 ≠ 0) :
    ∀ l : List ℕ, (∀ z ∈ l, 1 ≤ z) →
      Multiset.card (rootsIn h) ≤ Multiset.card (rootsIn (tOps l h)) + l.length := by
  intro l
  induction l with
  | nil => intro _; rw [tOps, List.length_nil, Nat.add_zero]
  | cons z l ih =>
    intro hl
    have h1 := ih fun w hw => hl w (List.mem_cons_of_mem z hw)
    have h2 := card_rootsIn_le (hl z List.mem_cons_self) (h := tOps l h)
      (by rw [eval_zero_tOps]; exact h0)
    rw [tOps, List.length_cons]
    omega

end CoefficientMass
