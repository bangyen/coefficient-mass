/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.VertexOpt
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Vertex Certificate Is Necessary

This module proves the necessity part of Lemma 6.11 of `coefficient-mass-rows.tex`.  The
one-sided derivative of `t ↦ Φ_r(r_Z + t d)` at `0⁺` is
`∑_{s ≥ 1} sgn(r_Z(s)) d(s) r^{-s} + ∑_{r_Z(s) = 0} |d(s)| r^{-s}` by dominated convergence;
if `r_Z` is optimal then it is nonnegative, and `d = ±e_y` gives `|G_y| ≤ |e_y(y)| r^{-y}`.

## Theorems

* `abs_add_mul_sub`.
* `tendsto_rowPhi_dir`.
* `mem_of_confPolyP_eval_eq_zero`.
* `tsum_zero_eY`.
* `cert_of_rowPhi_le`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `|a + tb| - |a| = t(sgn(a) b + [a = 0] |b|)` when `a = 0` or `t|b| ≤ |a|`. -/
theorem abs_add_mul_sub {a b t : ℝ} (ht : 0 < t) (h : a = 0 ∨ t * |b| ≤ |a|) :
    |a + t * b| - |a| = t * (Real.sign a * b + (if a = 0 then |b| else 0)) := by
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self b) ht.le
  have h2 := mul_le_mul_of_nonneg_left (neg_abs_le b) ht.le
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hb := h.resolve_left ha.ne
    rw [abs_of_neg ha] at hb
    rw [Real.sign_of_neg ha, if_neg ha.ne, abs_of_neg ha, abs_of_nonpos (by linarith)]
    ring
  · rw [Real.sign_zero, if_pos rfl, zero_add, abs_zero, sub_zero, abs_mul, abs_of_pos ht]
    ring
  · have hb := h.resolve_left ha.ne'
    rw [abs_of_pos ha] at hb
    rw [Real.sign_of_pos ha, if_neg ha.ne', abs_of_pos ha, abs_of_nonneg (by linarith)]
    ring

/-- `(Φ_r(p + t d) - Φ_r(p))/t → ∑ sgn(p(s)) d(s) r^{-s} + ∑_{p(s) = 0} |d(s)| r^{-s}` as
`t → 0⁺`. -/
theorem tendsto_rowPhi_dir {r : ℝ} (hr : 1 < r) (p d : ℝ[X]) :
    Tendsto (fun t : ℝ => (rowPhi r (p + C t * d) - rowPhi r p) / t) (𝓝[>] 0)
      (𝓝 ((∑' k : ℕ, Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) *
        (1 / r) ^ (k + 1)) + ∑' k : ℕ, (if p.eval ((k + 1 : ℕ) : ℝ) = 0 then
          |d.eval ((k + 1 : ℕ) : ℝ)| else 0) * (1 / r) ^ (k + 1))) := by
  have hfun : ∀ t : ℝ, 0 < t → (rowPhi r (p + C t * d) - rowPhi r p) / t =
      ∑' k : ℕ, (|p.eval ((k + 1 : ℕ) : ℝ) + t * d.eval ((k + 1 : ℕ) : ℝ)| -
        |p.eval ((k + 1 : ℕ) : ℝ)|) / t * (1 / r) ^ (k + 1) := fun t _ => by
    unfold rowPhi
    rw [← (summable_rowPhi hr _).tsum_sub (summable_rowPhi hr p), div_eq_mul_inv,
      ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [eval_add, eval_mul, eval_C]
    ring
  have hlim : ∀ k : ℕ, Tendsto (fun t : ℝ => (|p.eval ((k + 1 : ℕ) : ℝ) +
      t * d.eval ((k + 1 : ℕ) : ℝ)| - |p.eval ((k + 1 : ℕ) : ℝ)|) / t * (1 / r) ^ (k + 1))
      (𝓝[>] 0) (𝓝 ((Real.sign (p.eval ((k + 1 : ℕ) : ℝ)) * d.eval ((k + 1 : ℕ) : ℝ) +
        (if p.eval ((k + 1 : ℕ) : ℝ) = 0 then |d.eval ((k + 1 : ℕ) : ℝ)| else 0)) *
          (1 / r) ^ (k + 1))) := fun k => by
    set a := p.eval ((k + 1 : ℕ) : ℝ)
    set b := d.eval ((k + 1 : ℕ) : ℝ)
    have key : ∀ t : ℝ, 0 < t → (a = 0 ∨ t * |b| ≤ |a|) →
        (|a + t * b| - |a|) / t * (1 / r) ^ (k + 1) =
          (Real.sign a * b + (if a = 0 then |b| else 0)) * (1 / r) ^ (k + 1) := fun t ht h => by
      rw [abs_add_mul_sub ht h, mul_div_cancel_left₀ _ ht.ne']
    refine tendsto_nhds_of_eventually_eq ?_
    by_cases ha : a = 0
    · exact eventually_mem_nhdsWithin.mono fun t ht => key t ht (Or.inl ha)
    · have hpos : 0 < |a| / (|b| + 1) := div_pos (abs_pos.2 ha) (by positivity)
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT hpos) fun t ht => key t ht.1 (Or.inr ?_)
      have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |b| + 1)).1 ht.2
      nlinarith [ht.1, abs_nonneg b]
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ k : ℕ,
      ‖(|p.eval ((k + 1 : ℕ) : ℝ) + t * d.eval ((k + 1 : ℕ) : ℝ)| -
        |p.eval ((k + 1 : ℕ) : ℝ)|) / t * (1 / r) ^ (k + 1)‖ ≤
          |d.eval ((k + 1 : ℕ) : ℝ)| * (1 / r) ^ (k + 1) :=
    eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) k => by
      have h := abs_abs_sub_abs_le_abs_sub (p.eval ((k + 1 : ℕ) : ℝ) +
        t * d.eval ((k + 1 : ℕ) : ℝ)) (p.eval ((k + 1 : ℕ) : ℝ))
      rw [add_sub_cancel_left, abs_mul, abs_of_pos ht] at h
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos ht,
        abs_of_pos (by positivity : (0 : ℝ) < (1 / r) ^ (k + 1))]
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ ht).2 (by linarith)) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence (summable_rowPhi hr d) hlim hbound
  simp only [add_mul] at h
  rw [(summable_sign_mul hr p d).tsum_add (summable_zero_mul hr p d)] at h
  exact h.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hfun t ht).symm)

theorem mem_of_confPolyP_eval_eq_zero {Z : Finset ℕ} {x : ℕ}
    (h : (confPolyP Z).eval (x : ℝ) = 0) : x ∈ Z := by
  rw [eval_confPolyP, Finset.prod_eq_zero_iff] at h
  obtain ⟨z, hz, h⟩ := h
  have hz0 : (z : ℝ) ≠ 0 := fun h' => by
    rw [h', div_zero, sub_zero] at h
    exact one_ne_zero h
  have hxz : (x : ℝ) = z := (div_eq_one_iff_eq hz0).1 (by linarith)
  rw [Nat.cast_inj.1 hxz]
  exact hz

/-- `∑_{r_Z(s) = 0} |d(s)| r^{-s} = |e_y(y)| r^{-y}` for `d = ±e_y`. -/
theorem tsum_zero_eY {r : ℝ} {Z : Finset ℕ} (h0 : 0 ∉ Z) {y : ℕ} (hy : y ∈ Z) {d : ℝ[X]}
    (hd : ∀ x : ℝ, |d.eval x| = |(eY Z y).eval x|) :
    ∑' k : ℕ, (if (confPolyP Z).eval ((k + 1 : ℕ) : ℝ) = 0 then |d.eval ((k + 1 : ℕ) : ℝ)|
      else 0) * (1 / r) ^ (k + 1) = |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y := by
  have hy1 : y - 1 + 1 = y := Nat.sub_add_cancel (Nat.pos_of_ne_zero fun h : y = 0 => h0 (h ▸ hy))
  rw [tsum_eq_single (y - 1) fun k hk => by
      split_ifs with hz
      · rw [hd, eval_eY_mem h0 (mem_of_confPolyP_eval_eq_zero hz) (by omega), abs_zero,
          zero_mul]
      · rw [zero_mul],
    hy1, if_pos (confPolyP_eval_mem hy fun h : y = 0 => h0 (h ▸ hy)), hd]

/-- Lemma 6.11 of `coefficient-mass-rows.tex`, necessity: if `Φ_r(Z) ≤ Φ_r(q)` for every
admissible `q` of `μ_r(S, |Z| + 1)`, then `|G_y| ≤ |e_y(y)| r^{-y}` for every `y ∈ Z \ S`. -/
theorem cert_of_rowPhi_le {r : ℝ} (hr : 1 < r) {S Z : Finset ℕ} (hSZ : S ⊆ Z) (h0 : 0 ∉ Z)
    (hopt : ∀ q : ℝ[X], q.degree < ↑(Z.card + 1) → q.eval 0 = 1 →
      (∀ s ∈ S, q.eval (s : ℝ) = 0) → rowPhi r (confPolyP Z) ≤ rowPhi r q) :
    ∀ y ∈ Z \ S, |gY r Z y| ≤ |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y := by
  intro y hy
  obtain ⟨hyZ, hyS⟩ := Finset.mem_sdiff.1 hy
  obtain ⟨-, hp0, hpZ⟩ := confPolyP_admissible (L := Z.card + 1) h0 (by omega)
  have hdir : ∀ d : ℝ[X], d.natDegree ≤ Z.card → d.eval 0 = 0 →
      (∀ s ∈ S, d.eval (s : ℝ) = 0) → (∀ x : ℝ, |d.eval x| = |(eY Z y).eval x|) →
      0 ≤ (∑' k : ℕ, Real.sign ((confPolyP Z).eval ((k + 1 : ℕ) : ℝ)) *
        d.eval ((k + 1 : ℕ) : ℝ) * (1 / r) ^ (k + 1)) +
          |(eY Z y).eval (y : ℝ)| * (1 / r) ^ y := fun d hdn hd0 hdS habs => by
    rw [← tsum_zero_eY (r := r) h0 hyZ habs]
    refine ge_of_tendsto (tendsto_rowPhi_dir hr (confPolyP Z) d)
      (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => div_nonneg (sub_nonneg.2 ?_) ht.le)
    refine hopt _ ?_ ?_ fun s hs => ?_
    · have hn : (confPolyP Z + C t * d).natDegree ≤ Z.card :=
        (natDegree_add_le _ _).trans (max_le (natDegree_confPolyP Z)
          ((natDegree_C_mul_le _ _).trans hdn))
      exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
    · rw [eval_add, eval_mul, eval_C, hp0, hd0, mul_zero, add_zero]
    · rw [eval_add, eval_mul, eval_C, hpZ s (hSZ hs), hdS s hs, mul_zero, add_zero]
  have heS : ∀ s ∈ S, (eY Z y).eval (s : ℝ) = 0 := fun s hs =>
    eval_eY_mem h0 (hSZ hs) fun h : s = y => hyS (h ▸ hs)
  have h1 := hdir (eY Z y) (natDegree_eY_le hyZ) (eval_eY_zero Z y) heS fun _ => rfl
  have h2 := hdir (-eY Z y) (by rw [natDegree_neg]; exact natDegree_eY_le hyZ)
    (by rw [eval_neg, eval_eY_zero, neg_zero]) (fun s hs => by rw [eval_neg, heS s hs, neg_zero])
    fun x => by rw [eval_neg, abs_neg]
  rw [← gY] at h1
  simp only [eval_neg, mul_neg, neg_mul, tsum_neg] at h2
  rw [← gY] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

end CoefficientMass
