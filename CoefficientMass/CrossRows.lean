/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Crossing
import CoefficientMass.Insert
import CoefficientMass.RowValueDual

/-!
# One Insertion Covers Every Later Position

This module proves Theorem 4.3 of `coefficient-mass-rows.tex`.  Let `h = h_t(W)` be the
first gap of `W` above `t` and `W' = ins(W, h)`.  For `σ > t` the polynomials `r_W` and
`r_{W'}` vanish on `T ⊆ W ∩ [1, t]`, and at `σ` one of them vanishes (`σ < h` lies in `W`,
`σ = h` in `W'`) or they have opposite signs (Lemma 4.2); Lemma 4.1(a) then bounds
`μ_r(T ∪ {σ}, |W| + 2)`.  With `T` the exempted set of Proposition 2.1(a) without its
largest element this bounds `b_k(F)` from below.

## Definitions

* `firstGap`.
* `CrossRows`.

## Theorems

* `exists_gap`.
* `firstGap_spec`.
* `muR_insert_le`.
* `inv_muR_le_kthMag`.
* `crossRows`.
-/

open Polynomial

namespace CoefficientMass

theorem exists_gap (t : ℕ) (W : Finset ℕ) : ∃ x, t < x ∧ x ∉ W :=
  ⟨max t (W.sup id) + 1, by omega, fun h => by
    have := Finset.le_sup (f := id) h
    simp only [id_eq] at this
    omega⟩

/-- `h_t(W)`: the least integer above `t` not in `W`. -/
noncomputable def firstGap (t : ℕ) (W : Finset ℕ) : ℕ :=
  Nat.find (exists_gap t W)

theorem firstGap_spec (t : ℕ) (W : Finset ℕ) :
    t < firstGap t W ∧ firstGap t W ∉ W ∧ ∀ x, t < x → x < firstGap t W → x ∈ W := by
  classical
  have h := Nat.find_spec (exists_gap t W)
  refine ⟨h.1, h.2, fun x htx hx => ?_⟩
  by_contra hxW
  exact Nat.find_min (exists_gap t W) hx ⟨htx, hxW⟩

/-- Theorem 4.3 of `coefficient-mass-rows.tex`: for `r > 1`, `t ≥ 0`, finite
`W ⊂ ℕ_{>0}`, `T ⊆ W ∩ [1, t]` and `h = h_t(W)`,
`μ_r(T ∪ {σ}, |W| + 2) ≤ max(Φ_r(W), Φ_r(ins(W, h)))` for every integer `σ > t`.
Consequently, if `F` is a monic multiple of `(x - r)^L` and `J` carries `k - 1 ≥ 1` largest
nonleading magnitudes, with backward distances `S`, `t = max(S \ {max S})` and
`W ⊇ S \ {max S}` with `|W| ≤ L - 2`, then
`b_k(F) ≥ 1/max(Φ_r(W), Φ_r(ins(W, h_t(W))))`. -/
def CrossRows : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ (t : ℕ) (W T : Finset ℕ) (σ : ℕ), 0 ∉ W → T ⊆ W → (∀ x ∈ T, x ≤ t) → t < σ →
      muR r (insert σ T) (W.card + 2) ≤
        max (rowPhi r (confPolyP W)) (rowPhi r (confPolyP (ins W (firstGap t W))))) ∧
    ∀ (L k : ℕ) (F : ℝ[X]) (J W : Finset ℕ), F.Monic → (X - C r) ^ L ∣ F →
      J ⊆ Finset.range F.natDegree → J.card + 1 = k →
      (∀ i ∈ J, ∀ j < F.natDegree, j ∉ J → ‖F.coeff j‖ ≤ ‖F.coeff i‖) →
      ∀ hS : (J.image fun j => F.natDegree - j).Nonempty,
        (J.image fun j => F.natDegree - j).erase ((J.image fun j => F.natDegree - j).max' hS) ⊆
          W → 0 ∉ W → W.card + 2 ≤ L →
        1 / max (rowPhi r (confPolyP W)) (rowPhi r (confPolyP (ins W (firstGap
          (((J.image fun j => F.natDegree - j).erase
            ((J.image fun j => F.natDegree - j).max' hS)).sup id) W)))) ≤ kthMag F k

/-- The first claim of Theorem 4.3 of `coefficient-mass-rows.tex`. -/
theorem muR_insert_le {r : ℝ} (hr : 1 < r) (t : ℕ) (W T : Finset ℕ) (σ : ℕ) (h0 : 0 ∉ W)
    (hTW : T ⊆ W) (hTt : ∀ x ∈ T, x ≤ t) (hσ : t < σ) :
    muR r (insert σ T) (W.card + 2) ≤
      max (rowPhi r (confPolyP W)) (rowPhi r (confPolyP (ins W (firstGap t W)))) := by
  classical
  obtain ⟨hth, hhW, hbelow⟩ := firstGap_spec t W
  set h := firstGap t W
  obtain ⟨hlow, hhW', hcard, hflip⟩ := insFlip W h h0 (by omega) hhW
  have h0' : 0 ∉ ins W h := fun hz => by
    have : (0 : ℕ) ∈ (ins W h).filter (· < h) := Finset.mem_filter.2 ⟨hz, by omega⟩
    rw [hlow] at this
    exact h0 (Finset.mem_filter.1 this).1
  have hT0 : 0 ∉ T := fun hz => h0 (hTW hz)
  have hσT : σ ∉ T := fun hs => by have := hTt σ hs; omega
  have hadm₁ := confPolyP_admissible (L := W.card + 2) h0 (by omega)
  have hadm₂ := confPolyP_admissible (L := W.card + 2) h0' (by rw [hcard]; omega)
  have hTW' : T ⊆ ins W h := fun x hx => by
    have : x ∈ (ins W h).filter (· < h) := by
      rw [hlow]
      exact Finset.mem_filter.2 ⟨hTW hx, by have := hTt x hx; omega⟩
    exact (Finset.mem_filter.1 this).1
  have hsign : (confPolyP W).eval (σ : ℝ) * (confPolyP (ins W h)).eval (σ : ℝ) ≤ 0 := by
    rcases lt_trichotomy σ h with hσh | hσh | hσh
    · rw [confPolyP_eval_mem (hbelow σ hσ hσh) (by omega), zero_mul]
    · rw [hσh, confPolyP_eval_mem hhW' (by omega), mul_zero]
    · by_cases hσW : σ ∈ W
      · rw [confPolyP_eval_mem hσW (by omega), zero_mul]
      by_cases hσW' : σ ∈ ins W h
      · rw [confPolyP_eval_mem hσW' (by omega), mul_zero]
      have := hflip σ hσh hσW hσW'
      rw [confPoly_eq_eval, confPoly_eq_eval] at this
      exact this.le
  exact ((crossing r hr).1 (W.card + 2) _ T σ (confPolyP W) (confPolyP (ins W h)) hT0
    (by omega) hσT hadm₁.1 hadm₂.1 hadm₁.2.1 hadm₂.2.1 (fun s hs => hadm₁.2.2 s (hTW hs))
    (fun s hs => hadm₂.2.2 s (hTW' hs)) (le_max_left _ _) (le_max_right _ _) hsign).2

/-- `b_k(F) ≥ 1/μ_r(S, m)` for the exempted set `S` of Proposition 2.1(a) of
`coefficient-mass-rows.tex` and `m ≤ L`. -/
theorem inv_muR_le_kthMag {r : ℝ} (hr : 1 < r) {L k m : ℕ} {F : ℝ[X]} {J : Finset ℕ}
    (hF : F.Monic) (hdvd : (X - C r) ^ L ∣ F) (hJ : J ⊆ Finset.range F.natDegree)
    (hJc : J.card + 1 = k) (hdom : ∀ i ∈ J, ∀ j < F.natDegree, j ∉ J → ‖F.coeff j‖ ≤ ‖F.coeff i‖)
    (hmL : m ≤ L) (hJm : J.card < m) :
    1 / muR r (J.image fun j => F.natDegree - j) m ≤ kthMag F k := by
  set S := J.image fun j => F.natDegree - j
  have hS0 : 0 ∉ S := fun h => by
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 h
    have := Finset.mem_range.1 (hJ hj)
    omega
  have hSc : S.card < m := Finset.card_image_le.trans_lt hJm
  have hLD := le_natDegree_of_dvd hF hdvd
  have hkD : k ≤ F.natDegree := by
    have := Finset.card_le_card hJ
    rw [Finset.card_range] at this
    omega
  have hk : 1 ≤ k := by omega
  have hcert := (rowValueCert r L k F J hr hF hdvd hJ hJc hdom).1
  -- every admissible `q` has `1/Φ_r(q) ≤ b_k(F)`
  have hq : ∀ q : ℝ[X], q.degree < m → q.eval 0 = 1 → (∀ s ∈ S, q.eval (s : ℝ) = 0) →
      1 / rowPhi r q ≤ kthMag F k := fun q hq hq0 hqS =>
    (le_largeCount_iff hk hkD).1 (hcert q (hq.trans_le (by exact_mod_cast hmL)) hq0
      fun j hj => hqS _ (Finset.mem_image_of_mem _ hj))
  obtain ⟨hc, hc0, hcS⟩ := confPolyP_admissible hS0 hSc
  have hΦpos : 0 < rowPhi r (confPolyP S) :=
    (muR_pos hr hS0 hSc).trans_le (ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by
        have : 0 < 1 / r := by positivity
        positivity⟩
      (⟨confPolyP S, hc, hc0, hcS⟩ :
        {q : ℝ[X] // q.degree < m ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0}))
  have hb : 0 < kthMag F k := lt_of_lt_of_le (by positivity) (hq _ hc hc0 hcS)
  haveI : Nonempty {q : ℝ[X] // q.degree < m ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, hc, hc0, hcS⟩⟩
  have hμ : 1 / kthMag F k ≤ muR r S m := le_ciInf fun q => by
    obtain ⟨q, hq', hq0, hqS⟩ := q
    change 1 / kthMag F k ≤ rowPhi r q
    have h1 := hq q hq' hq0 hqS
    have hΦ : 0 < rowPhi r q := (muR_pos hr hS0 hSc).trans_le (ciInf_le ⟨0, by
      rintro _ ⟨q', rfl⟩
      exact tsum_nonneg fun _ => by
        have : 0 < 1 / r := by positivity
        positivity⟩
      (⟨q, hq', hq0, hqS⟩ :
        {q : ℝ[X] // q.degree < m ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0}))
    rw [div_le_iff₀ hb]
    rw [div_le_iff₀ hΦ] at h1
    linarith
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hμ)]
  rw [div_le_iff₀ hb] at hμ
  linarith

theorem crossRows : CrossRows := by
  intro r hr
  refine ⟨fun t W T σ h0 hTW hTt hσ => muR_insert_le hr t W T σ h0 hTW hTt hσ,
    fun L k F J W hF hdvd hJ hJc hdom hS hSW hW0 hWL => ?_⟩
  set S := J.image fun j => F.natDegree - j
  set σ := S.max' hS
  set T := S.erase σ
  set t := T.sup id
  have hTt : ∀ x ∈ T, x ≤ t := fun x hx => Finset.le_sup (f := id) hx
  have hS0 : 0 ∉ S := fun h => by
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 h
    have := Finset.mem_range.1 (hJ hj)
    omega
  have hσ0 : 0 < σ := Nat.pos_of_ne_zero fun h => hS0 (h ▸ S.max'_mem hS)
  have hσt : t < σ := (Finset.sup_lt_iff hσ0).2 fun x hx =>
    lt_of_le_of_ne (S.le_max' x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hins : insert σ T = S := Finset.insert_erase (S.max'_mem hS)
  have hμ := muR_insert_le hr t W T σ hW0 hSW hTt hσt
  rw [hins] at hμ
  have hJm : J.card < W.card + 2 := by
    have := Finset.card_le_card hSW
    rw [Finset.card_erase_of_mem (S.max'_mem hS)] at this
    have hSJ : S.card = J.card := Finset.card_image_of_injOn fun a ha b hb hab => by
      have := Finset.mem_range.1 (hJ ha)
      have := Finset.mem_range.1 (hJ hb)
      have h' : F.natDegree - a = F.natDegree - b := hab
      omega
    omega
  have hb := inv_muR_le_kthMag hr hF hdvd hJ hJc hdom hWL hJm
  have hμpos : 0 < muR r S (W.card + 2) :=
    muR_pos hr hS0 (Finset.card_image_le.trans_lt hJm)
  exact (one_div_le_one_div_of_le hμpos hμ).trans hb

end CoefficientMass
