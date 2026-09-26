/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarZerosPhi

/-!
# Several Far Zeros

This module proves Lemma 6.18 of `coefficient-mass-rows.tex`.  Since `Δ_{q,m}(t) → -Ψ_r(q) < 0`,
some least integer `t_m(q) ≥ 1` has `Δ_{q,m}(t_m(q)) ≤ 0`, and `Δ_{q,m}` does not increase.  If
`|U| ≤ m` and `U ⊂ [t, ∞)` with `Δ_{q,m}(t) ≤ 0`, then with `u = min U`,
`|r_U(s)| ≤ |1 - s/u| max(1, s/u)^{m-1}`, so `u(|r_U(s)| - 1) ≤ φ_m(s, u)` and
`u(Φ_r(q r_U) - Φ_r(q)) ≤ Δ_{q,m}(u) ≤ 0`.

## Definitions

* `tM`.
* `FarZeros`.

## Theorems

* `exists_deltaQ_nonpos`.
* `tM_spec`.
* `abs_confPolyP_le`.
* `mul_abs_confPolyP_sub_le`.
* `rowPhi_mul_confPolyP_le`.
* `farZeros`.
-/

open Polynomial Filter Topology

namespace CoefficientMass

/-- `t_m(q)`: the least integer `t ≥ 1` with `Δ_{q,m}(t) ≤ 0`. -/
noncomputable def tM (r : ℝ) (q : ℝ[X]) (m : ℕ) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧ deltaQ r q m t ≤ 0}

/-- Lemma 6.18 of `coefficient-mass-rows.tex`: for `r > 1`, `m ≥ 1` and `q ≠ 0`, (a)
`Δ_{q,m}` does not increase on `t > 0`, `Δ_{q,m} ≤ Δ_{q,m+1}`, `Δ_{q,m}(t) → -Ψ_r(q) < 0`; the
least integer `t_m(q) ≥ 1` with `Δ_{q,m}(t_m(q)) ≤ 0` has `Δ_{q,m}(t) ≤ 0` for real
`t ≥ t_m(q)`, and `t_m(q) ≤ t_{m+1}(q)`; (b) if `t > 0`, `Δ_{q,m}(t) ≤ 0`, `|U| ≤ m` and
`U ⊂ [t, ∞)`, then `Φ_r(q r_U) ≤ Φ_r(q)`.  Also `Δ_{q,1}(σ) = 2R_q(σ) - Ψ_r(q)`. -/
def FarZeros : Prop :=
  ∀ r : ℝ, 1 < r → ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ[X], q ≠ 0 →
    (∀ t t' : ℝ, 0 < t → t ≤ t' → deltaQ r q m t' ≤ deltaQ r q m t) ∧
    (∀ t : ℝ, 0 < t → deltaQ r q m t ≤ deltaQ r q (m + 1) t) ∧
    Tendsto (deltaQ r q m) atTop (𝓝 (-psiR r q)) ∧ 0 < psiR r q ∧
    1 ≤ tM r q m ∧ deltaQ r q m (tM r q m) ≤ 0 ∧
    (∀ t : ℕ, 1 ≤ t → t < tM r q m → 0 < deltaQ r q m t) ∧
    (∀ t : ℝ, (tM r q m : ℝ) ≤ t → deltaQ r q m t ≤ 0) ∧ tM r q m ≤ tM r q (m + 1) ∧
    (∀ (t : ℝ) (U : Finset ℕ), 0 < t → deltaQ r q m t ≤ 0 → U.card ≤ m → (∀ v ∈ U, t ≤ v) →
      rowPhi r (q * confPolyP U) ≤ rowPhi r q) ∧
    ∀ σ : ℝ, 0 < σ → deltaQ r q 1 σ = 2 * remR r q σ - psiR r q

theorem exists_deltaQ_nonpos {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) {q : ℝ[X]} (hq : q ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ deltaQ r q m t ≤ 0 := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_deltaQ hr hm q).eventually
    (gt_mem_nhds (neg_lt_zero.2 (psiR_pos hr hq))))
  refine ⟨max ⌈T⌉₊ 1, le_max_right _ _, (hT _ ?_).le⟩
  exact (Nat.le_ceil T).trans (by exact_mod_cast le_max_left _ _)

theorem tM_spec {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) {q : ℝ[X]} (hq : q ≠ 0) :
    1 ≤ tM r q m ∧ deltaQ r q m (tM r q m) ≤ 0 :=
  Nat.sInf_mem (exists_deltaQ_nonpos hr hm hq)

/-- `|r_U(s)| ≤ |1 - s/u| max(1, s/u)^{m-1}` for `u = min U > 0` and `|U| ≤ m`. -/
theorem abs_confPolyP_le {U : Finset ℕ} (hne : U.Nonempty) (hu0 : (0 : ℝ) < U.min' hne)
    {m : ℕ} (hU : U.card ≤ m) (s : ℕ) :
    |(confPolyP U).eval (s : ℝ)| ≤ |-(1 / (U.min' hne : ℝ)) * s + 1| *
      max 1 ((s : ℝ) / U.min' hne) ^ (m - 1) := by
  set u := U.min' hne
  have huU : u ∈ U := U.min'_mem hne
  have hfac : ∀ v ∈ U, |(C (-(1 / (v : ℝ))) * X + C 1).eval (s : ℝ)| ≤ max 1 ((s : ℝ) / u) :=
    fun v hv => by
      have hv' : (u : ℝ) ≤ v := by exact_mod_cast U.min'_le v hv
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      rw [eval_add, eval_mul, eval_C, eval_X, eval_C, abs_le]
      have h1 : 1 / (v : ℝ) * s ≤ s / u := by
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_left hs0 hu0 hv'
      have h2 : 0 ≤ 1 / (v : ℝ) * s := by
        have : (0 : ℝ) < v := hu0.trans_le hv'
        positivity
      constructor
      · linarith [le_max_right 1 ((s : ℝ) / u)]
      · linarith [le_max_left 1 ((s : ℝ) / u)]
  rw [confPolyP, eval_prod, Finset.abs_prod, ← Finset.mul_prod_erase U _ huU]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  · rw [eval_add, eval_mul, eval_C, eval_X, eval_C]
  · calc ∏ v ∈ U.erase u, |(C (-(1 / (v : ℝ))) * X + C 1).eval (s : ℝ)|
        ≤ ∏ _v ∈ U.erase u, max 1 ((s : ℝ) / u) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun v hv =>
            hfac v (Finset.mem_of_mem_erase hv)
      _ = max 1 ((s : ℝ) / u) ^ (U.card - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem huU]
      _ ≤ max 1 ((s : ℝ) / u) ^ (m - 1) := pow_le_pow_right₀ (le_max_left _ _) (by omega)

/-- `u (|r_U(s)| - 1) ≤ φ_m(s, u)` for `u = min U > 0` and `|U| ≤ m`. -/
theorem mul_abs_confPolyP_sub_le {U : Finset ℕ} (hne : U.Nonempty) (hu0 : (0 : ℝ) < U.min' hne)
    {m : ℕ} (hU : U.card ≤ m) (s : ℕ) :
    (U.min' hne : ℝ) * (|(confPolyP U).eval (s : ℝ)| - 1) ≤ phiM m s (U.min' hne) := by
  set u := U.min' hne
  have h := abs_confPolyP_le hne hu0 hU s
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  refine (mul_le_mul_of_nonneg_left (by linarith : |(confPolyP U).eval (s : ℝ)| - 1 ≤
    |-(1 / (u : ℝ)) * s + 1| * max 1 ((s : ℝ) / u) ^ (m - 1) - 1) hu0.le).trans (le_of_eq ?_)
  have e : (u : ℝ) * (1 / u) = 1 := mul_one_div_cancel hu0.ne'
  unfold phiM
  split_ifs with hsu
  · rw [max_eq_left (by rw [div_le_one hu0]; exact hsu), one_pow, mul_one,
      abs_of_nonneg (by
        have : 1 / (u : ℝ) * s ≤ 1 := by rw [one_div_mul_eq_div, div_le_one hu0]; exact hsu
        linarith)]
    linear_combination (-(s : ℝ)) * e
  · push_neg at hsu
    have hq : 1 ≤ (s : ℝ) / u := by rw [le_div_iff₀ hu0]; linarith
    rw [max_eq_right hq, abs_of_neg (by
      have : 1 < 1 / (u : ℝ) * s := by rw [one_div_mul_eq_div, lt_div_iff₀ hu0]; linarith
      linarith)]
    have e2 : (s : ℝ) / u = 1 / u * s := by rw [one_div_mul_eq_div]
    rw [e2]
    linear_combination ((1 / (u : ℝ) * s) ^ (m - 1) * s) * e

/-- Lemma 6.18(b): `Φ_r(q r_U) ≤ Φ_r(q)` when `Δ_{q,m}(t) ≤ 0`, `|U| ≤ m` and `U ⊂ [t, ∞)`. -/
theorem rowPhi_mul_confPolyP_le {r : ℝ} (hr : 1 < r) {m : ℕ} (hm : 1 ≤ m) (q : ℝ[X]) {t : ℝ}
    (ht : 0 < t) (hΔ : deltaQ r q m t ≤ 0) {U : Finset ℕ} (hU : U.card ≤ m)
    (hUt : ∀ v ∈ U, t ≤ v) : rowPhi r (q * confPolyP U) ≤ rowPhi r q := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · rw [confPolyP, Finset.prod_empty, mul_one]
  have hu : t ≤ (U.min' hne : ℝ) := hUt _ (U.min'_mem hne)
  have hu0 : (0 : ℝ) < U.min' hne := ht.trans_le hu
  have hΔu := (deltaQ_anti hr hm q ht hu).trans hΔ
  have hs1 := summable_rowPhi hr (q * confPolyP U)
  have hs2 := summable_rowPhi hr q
  have key : (U.min' hne : ℝ) * (rowPhi r (q * confPolyP U) - rowPhi r q) ≤
      deltaQ r q m (U.min' hne) := by
    rw [rowPhi, rowPhi, ← hs1.tsum_sub hs2, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun d => ?_) ((hs1.sub hs2).mul_left _)
      (summable_deltaQ hr hm q hu0)
    have h := mul_abs_confPolyP_sub_le hne hu0 hU (d + 1)
    rw [eval_mul, abs_mul]
    have hx : 0 ≤ |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) := by positivity
    calc (U.min' hne : ℝ) * (|q.eval ((d + 1 : ℕ) : ℝ)| * |(confPolyP U).eval ((d + 1 : ℕ) : ℝ)| *
          (1 / r) ^ (d + 1) - |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1))
        = (U.min' hne : ℝ) * (|(confPolyP U).eval ((d + 1 : ℕ) : ℝ)| - 1) *
            (|q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) := by ring
      _ ≤ phiM m (d + 1) (U.min' hne) * (|q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_right h hx
      _ = _ := by ring
  nlinarith

theorem farZeros : FarZeros := by
  intro r hr m hm q hq
  obtain ⟨h1, h2⟩ := tM_spec hr hm hq
  refine ⟨fun t t' ht h => deltaQ_anti hr hm q ht h, fun t ht => deltaQ_le_succ hr hm q ht,
    tendsto_deltaQ hr hm q, psiR_pos hr hq, h1, h2, fun t ht htm => ?_,
    fun t ht => (deltaQ_anti hr hm q (by exact_mod_cast (show 0 < tM r q m by omega)) ht).trans h2,
    ?_, fun t U ht hΔ hU hUt => rowPhi_mul_confPolyP_le hr hm q ht hΔ hU hUt,
    fun σ hσ => deltaQ_one hr q hσ⟩
  · have := Nat.notMem_of_lt_sInf htm
    by_contra hle
    exact this ⟨ht, not_lt.1 hle⟩
  · obtain ⟨h1', h2'⟩ := tM_spec hr (by omega : 1 ≤ m + 1) hq
    exact Nat.sInf_le ⟨h1', (deltaQ_le_succ hr hm q (by exact_mod_cast (show 0 < tM r q (m + 1)
      by omega))).trans h2'⟩

end CoefficientMass
