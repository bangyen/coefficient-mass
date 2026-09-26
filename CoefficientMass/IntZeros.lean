/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.RowLast

/-!
# Vertices with Integer Zeros

This module proves the vertex step of Lemma 3.1 of `coefficient-mass-rows.tex`.  Let `N` be a
finite set of at least `n` positive integers and `ω > 0` on `N`.  Every real `p` with
`deg p < n` and `p(0) = 1` can be replaced by `r_Y = ∏_{y ∈ Y} (1 - s/y)` with `Y ⊆ N`,
`|Y| = n - 1`, without increasing `f(p) = ∑_{s ∈ N} ω(s) |p(s)|`.  If `p` has fewer than
`n - 1` zeros `Z` in `N`, the direction `e = s ∏_{z ∈ Z} (s - z)` keeps `p(0)` and the zeros;
along `±e` the sum is affine until a first new zero, and the sign making it nonincreasing
must meet one, since otherwise its slope `∑ ω |e|` would be positive.

## Definitions

* `nodeSum`.

## Theorems

* `abs_add_mul_eq`.
* `exists_vertex_step`.
* `exists_of_many_zeros`.
* `exists_int_zeros`.
-/

open Polynomial

namespace CoefficientMass

/-- `f(p) = ∑_{s ∈ N} ω(s) |p(s)|`. -/
noncomputable def nodeSum (ω : ℕ → ℝ) (N : Finset ℕ) (p : ℝ[X]) : ℝ :=
  ∑ s ∈ N, ω s * |p.eval (s : ℝ)|

/-- Before its sign changes, `|x + t y|` is affine in `t`. -/
theorem abs_add_mul_eq {x y t : ℝ} (ht : 0 ≤ t) (hxy : x = 0 → y = 0)
    (hcross : x * y < 0 → t ≤ -x / y) :
    |x + t * y| = |x| + t * (if 0 ≤ x then y else -y) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [if_neg (not_le.2 hx), abs_of_neg hx]
    rcases le_or_gt y 0 with hy | hy
    · rw [abs_of_nonpos (by nlinarith)]
      ring
    · have hc := hcross (mul_neg_of_neg_of_pos hx hy)
      rw [le_div_iff₀' hy] at hc
      · rw [abs_of_nonpos (by nlinarith)]
        ring
  · rw [hx, hxy hx, if_pos le_rfl]
    simp only [mul_zero, add_zero, abs_zero]
  · rw [if_pos hx.le, abs_of_pos hx]
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg (by nlinarith)]
    · have hc := hcross (mul_neg_of_pos_of_neg hx hy)
      rw [le_div_iff_of_neg hy] at hc
      rw [abs_of_nonneg (by nlinarith)]

/-- One step: a polynomial with fewer than `n - 1` zeros in `N` gains a zero without
increasing `f`. -/
theorem exists_vertex_step {ω : ℕ → ℝ} {N : Finset ℕ} (hω : ∀ s ∈ N, 0 < ω s)
    (hN0 : 0 ∉ N) {n : ℕ} (hNn : n ≤ N.card) {p : ℝ[X]} (hp : p.natDegree < n)
    (hp0 : p.eval 0 = 1)
    (hZ : (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card + 1 < n) :
    ∃ p' : ℝ[X], p'.natDegree < n ∧ p'.eval 0 = 1 ∧
      (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card <
        (N.filter fun s : ℕ => p'.eval (s : ℝ) = 0).card ∧
      nodeSum ω N p' ≤ nodeSum ω N p := by
  classical
  set Z := N.filter fun s : ℕ => p.eval (s : ℝ) = 0
  set e : ℝ[X] := X * ∏ z ∈ Z, (X - C (z : ℝ))
  have he : ∀ y : ℝ, e.eval y = y * ∏ z ∈ Z, (y - z) := fun y => by
    rw [eval_mul, eval_X, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  have he0 : e.eval 0 = 0 := by rw [he, zero_mul]
  have heZ : ∀ z ∈ Z, e.eval (z : ℝ) = 0 := fun z hz => by
    rw [he, Finset.prod_eq_zero hz (sub_self _), mul_zero]
  have heN : ∀ s ∈ N, s ∉ Z → e.eval (s : ℝ) ≠ 0 := fun s hs hsZ => by
    rw [he]
    refine mul_ne_zero (by exact_mod_cast fun h => hN0 (h ▸ hs)) (Finset.prod_ne_zero_iff.2
      fun z hz h => hsZ ?_)
    rw [sub_eq_zero, Nat.cast_inj] at h
    rwa [h]
  have hedeg : e.natDegree < n := by
    have h1 : e.natDegree ≤ 1 + Z.card :=
      (natDegree_mul_le).trans (add_le_add natDegree_X_le
        (natDegree_finset_prod_X_sub_C_eq_card Z fun z : ℕ => (z : ℝ)).le)
    omega
  -- the slope of `f` along `e`
  set g : ℕ → ℝ := fun s => if 0 ≤ p.eval (s : ℝ) then e.eval (s : ℝ) else -e.eval (s : ℝ)
  set c := ∑ s ∈ N, ω s * g s
  set σ : ℝ := if c ≤ 0 then 1 else -1
  have hσc : σ * c ≤ 0 := by
    simp only [σ]
    split_ifs with h
    · linarith
    · linarith
  have hσ : σ ≠ 0 := by simp only [σ]; split_ifs <;> norm_num
  set e' := C σ * e
  have he' : ∀ y, e'.eval y = σ * e.eval y := fun y => by rw [eval_mul, eval_C]
  -- the positions where the sign would change
  set B := N.filter fun s : ℕ => p.eval (s : ℝ) * e'.eval (s : ℝ) < 0
  have hB : B.Nonempty := by
    by_contra hB
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hB
    have hterm : ∀ s ∈ N, σ * (ω s * g s) = ω s * |e'.eval (s : ℝ)| := fun s hs => by
      have hps := not_lt.1 (hB hs)
      rw [he'] at hps ⊢
      simp only [g]
      rcases lt_trichotomy (p.eval (s : ℝ)) 0 with h | h | h
      · rw [if_neg (not_le.2 h), abs_of_nonpos (by nlinarith)]
        ring
      · rw [heZ s (Finset.mem_filter.2 ⟨hs, h⟩)]
        simp only [mul_zero, neg_zero, abs_zero, ite_self]
      · rw [if_pos h.le, abs_of_nonneg (by nlinarith)]
        ring
    obtain ⟨s₀, hs₀N, hs₀Z⟩ : ∃ s ∈ N, s ∉ Z := by
      by_contra h
      push_neg at h
      have := Finset.card_le_card (fun s hs => h s hs : N ⊆ Z)
      omega
    have hpos : 0 < ∑ s ∈ N, ω s * |e'.eval (s : ℝ)| :=
      Finset.sum_pos' (fun s hs => mul_nonneg (hω s hs).le (abs_nonneg _))
        ⟨s₀, hs₀N, mul_pos (hω s₀ hs₀N) (abs_pos.2 (by
          rw [he']; exact mul_ne_zero hσ (heN s₀ hs₀N hs₀Z)))⟩
    rw [← Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hpos
    exact absurd hσc (not_le.2 hpos)
  obtain ⟨s₁, hs₁B, hmin⟩ := B.exists_min_image
    (fun s : ℕ => -p.eval (s : ℝ) / e'.eval (s : ℝ)) hB
  set t := -p.eval (s₁ : ℝ) / e'.eval (s₁ : ℝ)
  obtain ⟨hs₁N, hs₁⟩ := Finset.mem_filter.1 hs₁B
  have hes₁ : e'.eval (s₁ : ℝ) ≠ 0 := fun h => by rw [h, mul_zero] at hs₁; exact lt_irrefl 0 hs₁
  have ht : 0 < t := by
    rcases lt_or_gt_of_ne hes₁ with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  refine ⟨p + C t * e', ?_, ?_, ?_, ?_⟩
  · refine (natDegree_add_le _ _).trans_lt (max_lt hp ?_)
    exact ((natDegree_C_mul_le _ _).trans (natDegree_C_mul_le _ _)).trans_lt hedeg
  · rw [eval_add, eval_mul, eval_C, he', he0, mul_zero, mul_zero, add_zero, hp0]
  · refine Finset.card_lt_card ⟨fun s hs => ?_, fun h => ?_⟩
    · obtain ⟨hsN, hs0⟩ := Finset.mem_filter.1 hs
      refine Finset.mem_filter.2 ⟨hsN, ?_⟩
      rw [eval_add, eval_mul, eval_C, he', heZ s hs, hs0, mul_zero, mul_zero, add_zero]
    · have htmul : t * e'.eval (s₁ : ℝ) = -p.eval (s₁ : ℝ) := div_mul_cancel₀ _ hes₁
      have := h (Finset.mem_filter.2 ⟨hs₁N, by
        rw [eval_add, eval_mul, eval_C, htmul, add_neg_cancel]⟩)
      rw [(Finset.mem_filter.1 this).2, zero_mul] at hs₁
      exact lt_irrefl 0 hs₁
  · have hstep : ∀ s ∈ N, |(p + C t * e').eval (s : ℝ)| =
        |p.eval (s : ℝ)| + t * (σ * g s) := fun s hs => by
      rw [eval_add, eval_mul, eval_C]
      have := abs_add_mul_eq (x := p.eval (s : ℝ)) (y := e'.eval (s : ℝ)) ht.le
        (fun hx => by
          rw [he', heZ s (Finset.mem_filter.2 ⟨hs, hx⟩), mul_zero])
        (fun hxy => hmin s (Finset.mem_filter.2 ⟨hs, hxy⟩))
      rw [this]
      simp only [g, he']
      split_ifs <;> ring
    have hsum : nodeSum ω N (p + C t * e') =
        ∑ s ∈ N, ω s * (|p.eval (s : ℝ)| + t * (σ * g s)) :=
      Finset.sum_congr rfl fun s hs => by rw [hstep s hs]
    have hsplit : ∑ s ∈ N, ω s * (|p.eval (s : ℝ)| + t * (σ * g s)) =
        nodeSum ω N p + t * (σ * c) := by
      simp only [nodeSum, c, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsum, hsplit]
    have := mul_nonpos_of_nonneg_of_nonpos ht.le hσc
    linarith

/-- With at least `n - 1` zeros in `N`, `p` is itself some `r_Y`. -/
theorem exists_of_many_zeros (ω : ℕ → ℝ) {N : Finset ℕ} (hN0 : 0 ∉ N) {n : ℕ} (hn : 1 ≤ n)
    {p : ℝ[X]} (hp : p.natDegree < n) (hp0 : p.eval 0 = 1)
    (hZ : n ≤ (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card + 1) :
    ∃ Y ⊆ N, Y.card + 1 = n ∧ nodeSum ω N (confPolyP Y) ≤ nodeSum ω N p := by
  obtain ⟨Y, hYZ, hYc⟩ := Finset.exists_subset_card_eq (show n - 1 ≤
    (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card by omega)
  have hY0 : 0 ∉ Y := fun h => hN0 (Finset.mem_filter.1 (hYZ h)).1
  have hq : p.degree < n := degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  have := eq_confPolyP_of_card hY0 (by omega) hq hp0 fun s hs =>
    (Finset.mem_filter.1 (hYZ hs)).2
  exact ⟨Y, fun s hs => (Finset.mem_filter.1 (hYZ hs)).1, by omega, by rw [← this]⟩

/-- Every `p` with `deg p < n` and `p(0) = 1` is beaten by some `r_Y`, `Y ⊆ N`,
`|Y| = n - 1`. -/
theorem exists_int_zeros {ω : ℕ → ℝ} {N : Finset ℕ} (hω : ∀ s ∈ N, 0 < ω s) (hN0 : 0 ∉ N)
    {n : ℕ} (hn : 1 ≤ n) (hNn : n ≤ N.card) :
    ∀ m : ℕ, ∀ p : ℝ[X], p.natDegree < n → p.eval 0 = 1 →
      n - (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card ≤ m →
        ∃ Y ⊆ N, Y.card + 1 = n ∧ nodeSum ω N (confPolyP Y) ≤ nodeSum ω N p := by
  intro m
  induction m with
  | zero =>
    intro p hp hp0 hm
    exact exists_of_many_zeros ω hN0 hn hp hp0 (by omega)
  | succ m ih =>
    intro p hp hp0 hm
    by_cases hZ : (N.filter fun s : ℕ => p.eval (s : ℝ) = 0).card + 1 < n
    · obtain ⟨p', hp', hp'0, hlt, hle⟩ := exists_vertex_step hω hN0 hNn hp hp0 hZ
      obtain ⟨Y, hYN, hYc, hY⟩ := ih p' hp' hp'0 (by omega)
      exact ⟨Y, hYN, hYc, hY.trans hle⟩
    · exact exists_of_many_zeros ω hN0 hn hp hp0 (by omega)

end CoefficientMass
