/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.IntZeros

/-!
# Integer Zero Sets Suffice

This module proves Lemma 3.1 of `coefficient-mass-rows.tex`.  Let `ω ≥ 0` vanish below `i`,
be positive from `i` on, and have `∑_s ω(s) (1 + s)^{n - 1} < ∞`.  The infimum of
`∑_s ω(s) |p(s)|` over real `p` with `deg p < n` and `p(0) = 1` equals the infimum over
`p = ∏_{y ∈ Y} (1 - s/y)` with `Y` a set of `n - 1` integers at least `i`.  By the vertex
step each `p` is beaten on `[i, D]` by such a product with `Y ⊆ [i, D]`, and
`|r_Y(s)| ≤ (1 + s)^{n - 1}` makes the part beyond `D` small.

## Definitions

* `wInf`.
* `IntZerosInf`.

## Theorems

* `abs_eval_le_pow`.
* `abs_confPolyP_le_pow`.
* `summable_weighted`.
* `tsum_eq_nodeSum_add`.
* `intZerosInf`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `inf_p ∑_s ω(s) |p(s)|` over real `p` with `deg p < n` and `p(0) = 1`. -/
noncomputable def wInf (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨅ p : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1}, ∑' s : ℕ, ω s * |p.1.eval (s : ℝ)|

/-- Lemma 3.1 of `coefficient-mass-rows.tex`: for `i, n ≥ 1` and `ω ≥ 0` vanishing below
`i`, positive from `i` on, with `∑_s ω(s) (1 + s)^{n - 1} < ∞`, the infimum `wInf ω n` is
attained along products `∏_{y ∈ Y} (1 - s/y)` over sets `Y` of `n - 1` integers `≥ i`. -/
def IntZerosInf : Prop :=
  ∀ (ω : ℕ → ℝ) (i n : ℕ), 1 ≤ i → 1 ≤ n → (∀ s, s < i → ω s = 0) → (∀ s, i ≤ s → 0 < ω s) →
    Summable (fun s : ℕ => ω s * (1 + (s : ℝ)) ^ (n - 1)) →
      wInf ω n = ⨅ Y : {Y : Finset ℕ // (∀ y ∈ Y, i ≤ y) ∧ Y.card + 1 = n},
        ∑' s : ℕ, ω s * |(confPolyP Y.1).eval (s : ℝ)|

/-- `|p(x)| ≤ (∑_j |p_j|) (1 + x)^{n - 1}` for `deg p < n` and `x ≥ 0`. -/
theorem abs_eval_le_pow {p : ℝ[X]} {n : ℕ} (hp : p.natDegree < n) {x : ℝ} (hx : 0 ≤ x) :
    |p.eval x| ≤ (∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j|) * (1 + x) ^ (n - 1) := by
  refine (abs_eval_le p hx).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hj := Finset.mem_range.1 hj
  calc x ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hx (by linarith) j
    _ ≤ (1 + x) ^ (n - 1) := pow_le_pow_right₀ (by linarith) (by omega)

/-- `|r_Y(x)| ≤ (1 + x)^{|Y|}` for `Y ⊂ ℕ_{>0}` and `x ≥ 0`. -/
theorem abs_confPolyP_le_pow {Y : Finset ℕ} (h0 : 0 ∉ Y) {x : ℝ} (hx : 0 ≤ x) :
    |(confPolyP Y).eval x| ≤ (1 + x) ^ Y.card := by
  rw [eval_confPolyP, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun y hy => ?_
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hy)
  have h1 : x / y ≤ x := div_le_self hx hy1
  have h2 : 0 ≤ x / y := div_nonneg hx (by linarith)
  rw [abs_le]
  constructor <;> linarith

theorem summable_weighted {ω : ℕ → ℝ} {n : ℕ} (hω : ∀ s, 0 ≤ ω s)
    (hsum : Summable fun s : ℕ => ω s * (1 + (s : ℝ)) ^ (n - 1)) (C : ℝ) {f : ℕ → ℝ}
    (hf : ∀ s, |f s| ≤ C * (1 + (s : ℝ)) ^ (n - 1)) : Summable fun s => ω s * |f s| :=
  Summable.of_nonneg_of_le (fun s => mul_nonneg (hω s) (abs_nonneg _))
    (fun s => by
      calc ω s * |f s| ≤ ω s * (C * (1 + (s : ℝ)) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left (hf s) (hω s)
        _ = C * (ω s * (1 + (s : ℝ)) ^ (n - 1)) := by ring)
    (hsum.mul_left C)

/-- `∑_s ω(s) |p(s)| = f_{[i, D]}(p) + ∑_{s > D} ω(s) |p(s)|` when `ω` vanishes below `i`. -/
theorem tsum_eq_nodeSum_add {ω : ℕ → ℝ} {i : ℕ} (hω0 : ∀ s, s < i → ω s = 0) {p : ℝ[X]}
    (hsum : Summable fun s : ℕ => ω s * |p.eval (s : ℝ)|) (D : ℕ) :
    ∑' s : ℕ, ω s * |p.eval (s : ℝ)| =
      nodeSum ω (Finset.Icc i D) p +
        ∑' s : ℕ, ω (s + (D + 1)) * |p.eval ((s + (D + 1) : ℕ) : ℝ)| := by
  rw [← hsum.sum_add_tsum_nat_add (D + 1), nodeSum]
  congr 1
  refine (Finset.sum_subset (fun s hs => Finset.mem_range.2 (by
    have := (Finset.mem_Icc.1 hs).2
    omega)) fun s hs hsIn => ?_).symm
  rw [hω0 s (by
    by_contra h
    exact hsIn (Finset.mem_Icc.2 ⟨not_lt.1 h, by have := Finset.mem_range.1 hs; omega⟩)), zero_mul]

theorem intZerosInf : IntZerosInf := by
  intro ω i n hi hn hω0 hωpos hsum
  have hω : ∀ s, 0 ≤ ω s := fun s => by
    rcases lt_or_ge s i with h | h
    · rw [hω0 s h]
    · exact (hωpos s h).le
  haveI : Nonempty {Y : Finset ℕ // (∀ y ∈ Y, i ≤ y) ∧ Y.card + 1 = n} :=
    ⟨⟨Finset.Icc i (i + n - 2), fun y hy => (Finset.mem_Icc.1 hy).1, by
      rw [Nat.card_Icc]; omega⟩⟩
  haveI : Nonempty {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one⟩⟩
  have hY0 : ∀ Y : Finset ℕ, (∀ y ∈ Y, i ≤ y) → 0 ∉ Y := fun Y hY h => by
    have := hY 0 h
    omega
  -- the summability of the products
  have hsumY : ∀ Y : Finset ℕ, (∀ y ∈ Y, i ≤ y) → Y.card + 1 = n →
      Summable fun s : ℕ => ω s * |(confPolyP Y).eval (s : ℝ)| := fun Y hY hYc =>
    summable_weighted hω hsum 1 fun s => by
      rw [one_mul, show n - 1 = Y.card by omega]
      exact abs_confPolyP_le_pow (hY0 Y hY) (Nat.cast_nonneg s)
  have hbdd : ∀ {ι : Type} (f : ι → ℝ), (∀ x, 0 ≤ f x) → BddBelow (Set.range f) :=
    fun f hf => ⟨0, by rintro _ ⟨x, rfl⟩; exact hf x⟩
  refine le_antisymm (le_ciInf fun Y => ?_) (le_ciInf fun p => ?_)
  · -- products are admissible
    obtain ⟨Y, hY, hYc⟩ := Y
    have hadm := confPolyP_admissible (L := n) (hY0 Y hY) (by omega)
    exact ciInf_le (hbdd _ fun q => tsum_nonneg fun s => mul_nonneg (hω s) (abs_nonneg _))
      (⟨confPolyP Y, hadm.1, hadm.2.1⟩ : {p : ℝ[X] // p.degree < n ∧ p.eval 0 = 1})
  · -- every `p` is beaten up to the tail
    obtain ⟨p, hp, hp0⟩ := p
    change _ ≤ ∑' s : ℕ, ω s * |p.eval (s : ℝ)|
    have hpne : p ≠ 0 := fun h => by rw [h, eval_zero] at hp0; exact zero_ne_one hp0
    have hpn : p.natDegree < n := by
      rw [degree_eq_natDegree hpne] at hp
      exact_mod_cast hp
    have hsump : Summable fun s : ℕ => ω s * |p.eval (s : ℝ)| :=
      summable_weighted hω hsum _ fun s => abs_eval_le_pow hpn (Nat.cast_nonneg s)
    set g : ℕ → ℝ := fun s => ω s * (1 + (s : ℝ)) ^ (n - 1)
    have htail : Tendsto (fun D : ℕ => ∑' s : ℕ, ω s * |p.eval (s : ℝ)| +
        ∑' k : ℕ, g (k + (D + 1))) atTop (𝓝 (∑' s : ℕ, ω s * |p.eval (s : ℝ)| + 0)) :=
      ((tendsto_sum_nat_add g).comp (tendsto_add_atTop_nat 1)).const_add _
    refine le_of_le_of_eq (ge_of_tendsto htail (Filter.eventually_atTop.2 ⟨i + n, fun D hD => ?_⟩))
      (add_zero _)
    have hNn : n ≤ (Finset.Icc i D).card := by rw [Nat.card_Icc]; omega
    obtain ⟨Y, hYN, hYc, hYle⟩ := exists_int_zeros (fun s hs => hωpos s (Finset.mem_Icc.1 hs).1)
      (fun h => by have := (Finset.mem_Icc.1 h).1; omega) hn hNn n p hpn hp0 (by omega)
    have hYi : ∀ y ∈ Y, i ≤ y := fun y hy => (Finset.mem_Icc.1 (hYN hy)).1
    have h1 := tsum_eq_nodeSum_add hω0 (hsumY Y hYi hYc) D
    have h2 := tsum_eq_nodeSum_add hω0 hsump D
    have htl : ∑' s : ℕ, ω (s + (D + 1)) * |(confPolyP Y).eval ((s + (D + 1) : ℕ) : ℝ)| ≤
        ∑' s : ℕ, g (s + (D + 1)) :=
      Summable.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left (by
          rw [show n - 1 = Y.card by omega]
          exact abs_confPolyP_le_pow (hY0 Y hYi) (Nat.cast_nonneg _)) (hω _))
        ((summable_nat_add_iff (D + 1)).2 (hsumY Y hYi hYc))
        ((summable_nat_add_iff (D + 1)).2 hsum)
    have htp : 0 ≤ ∑' s : ℕ, ω (s + (D + 1)) * |p.eval ((s + (D + 1) : ℕ) : ℝ)| :=
      tsum_nonneg fun s => mul_nonneg (hω _) (abs_nonneg _)
    have hle : ⨅ Y : {Y : Finset ℕ // (∀ y ∈ Y, i ≤ y) ∧ Y.card + 1 = n},
        ∑' s : ℕ, ω s * |(confPolyP Y.1).eval (s : ℝ)| ≤
          ∑' s : ℕ, ω s * |(confPolyP Y).eval (s : ℝ)| :=
      ciInf_le (hbdd _ fun Y' => tsum_nonneg fun s => mul_nonneg (hω s) (abs_nonneg _))
        (⟨Y, hYi, hYc⟩ : {Y : Finset ℕ // (∀ y ∈ Y, i ≤ y) ∧ Y.card + 1 = n})
    linarith

end CoefficientMass
