/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Displaced

/-!
# The Interlacing Bound

Lemma 2.3 of `coefficient-mass.tex` and the drive inequality it feeds.  The
correction `Δ = σ F̂ - E`, with `E_d = G_d - y_c G_{d-1}`, is a sum on the
smaller nodes.  If `Δ_d < 0` at some `d > m + 1`, then `Δ` weakly alternates
at the `|Z'| + 2` points `Z' ∪ {m + 1, d}`: at `p ∈ Z'` it equals
`y_c G_{p-1}`, whose sign the zeros of `G` fix, and `Δ_{m+1} = 0`.  That is
one alternation more than its node count allows.  Combined with
`theta_bound` this gives `μ E_d ≤ F̂_d` for `d ≥ z`.

## Theorems

* `drive`.
-/

namespace CoefficientMass

/-- The drive inequality `μ (G_{e+1} - y_c G_e) ≤ F̂_{e+1}` for `e + 1 ≥ z`. -/
theorem drive {n : ℕ} (y : Fin (n + 1) → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (Z : Finset ℕ) {z : ℕ} (hz : z ∈ Z) (hzmax : ∀ τ ∈ Z, τ ≤ z)
    (h0 : 0 ∉ Z) (hcard : Z.card = n) (aF : Fin n → ℝ)
    (hF : IsCertificate aF (fun i => y i.castSucc) (Z.erase z)) (aG : Fin (n + 1) → ℝ)
    (hG0 : ∀ k ∈ insert 0 (Z.erase z), expSum aG y k = 0) (hGz : expSum aG y z = 1)
    {m : ℕ} (hm : m ∈ insert 0 (Z.erase z)) (hmmax : ∀ τ ∈ Z.erase z, τ ≤ m)
    (hmz : m < z) (hμ : 0 < (-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) z)
    {e : ℕ} (he : z ≤ e + 1) :
    ((-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) z) *
        (expSum aG y (e + 1) - y (Fin.last n) * expSum aG y e) ≤
      (-1) ^ (Z.erase z).card * expSum aF (fun i => y i.castSucc) (e + 1) := by
  set η : ℝ := (-1) ^ (Z.erase z).card with hη
  set F := expSum aF (fun i => y i.castSucc) with hFdef
  set G := expSum aG y with hGdef
  set yc := y (Fin.last n)
  have hZ' : (Z.erase z).card + 1 = n := by
    rw [Finset.card_erase_of_mem hz, hcard]
    have := Finset.card_pos.2 ⟨z, hz⟩
    omega
  have h0' : 0 ∉ Z.erase z := fun h => h0 (Finset.mem_of_mem_erase h)
  have hA : (insert 0 (Z.erase z)).card + 1 = n + 1 := by
    rw [Finset.card_insert_of_notMem h0', hZ']
  have hAz : ∀ α ∈ insert 0 (Z.erase z), α < z := fun α hα => by
    rcases Finset.mem_insert.1 hα with rfl | hα
    · exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hz)
    · exact lt_of_le_of_ne (hzmax α (Finset.mem_of_mem_erase hα)) (Finset.ne_of_mem_erase hα)
  have hy' : Function.Injective fun i : Fin n => y i.castSucc :=
    hy.comp (Fin.castSucc_injective n)
  have hpos' : ∀ i : Fin n, 0 < y i.castSucc := fun i => hpos _
  have hηη : η * η = 1 := neg_one_pow_mul_self _
  have hFb : ∀ d, 0 < d → (∀ τ ∈ Z.erase z, τ < d) → 0 < η * F d := fun d hd hdZ => by
    have := sign_of_certificate aF _ hy' hpos' _ hZ' h0' hF hd fun h => lt_irrefl _ (hdZ d h)
    rwa [Finset.filter_true_of_mem hdZ] at this
  have hm1 : ∀ τ ∈ Z.erase z, τ < m + 1 := fun τ hτ => Nat.lt_succ_of_le (hmmax τ hτ)
  have hFm : 0 < η * F (m + 1) := hFb _ (Nat.succ_pos m) hm1
  set σ := G (m + 1) / (η * F (m + 1)) with hσ
  have hσμ : σ * (η * F z) ≤ 1 := by
    rw [hσ, div_mul_eq_mul_div, div_le_one hFm]
    exact theta_bound y hy hpos Z hz hzmax h0 hcard aF hF aG hG0 hGz hm hmmax hmz hμ
  have hΔ : ∀ e, expSum (fun i => σ * (η * aF i) -
      aG i.castSucc * (1 - yc / y i.castSucc)) (fun i => y i.castSucc) (e + 1) =
      σ * (η * F (e + 1)) - (G (e + 1) - yc * G e) := fun e => by
    rw [expSum_sub, expSum_mul_left, expSum_mul_left, expSum_correction aG y hpos]
  have hΔm : σ * (η * F (m + 1)) - (G (m + 1) - yc * G m) = 0 := by
    rw [hG0 m hm, mul_zero, sub_zero, hσ, div_mul_cancel₀ _ hFm.ne', sub_self]
  -- the interlacing bound `Δ ≥ 0` past `m + 1`
  have hint : ∀ e, m + 1 < e + 1 → 0 ≤ σ * (η * F (e + 1)) - (G (e + 1) - yc * G e) := by
    intro e hlt
    rw [← hΔ]
    by_contra hneg
    push_neg at hneg
    set S := insert (e + 1) (insert (m + 1) (Z.erase z)) with hS
    have hm1Z : m + 1 ∉ Z.erase z := fun h => lt_irrefl _ (hm1 _ h)
    have he1 : e + 1 ∉ insert (m + 1) (Z.erase z) := by
      rw [Finset.mem_insert]
      exact fun h => h.elim (fun h => hlt.ne' h) fun h => by have := hm1 _ h; omega
    have hScard : S.card = n + 1 := by
      rw [hS, Finset.card_insert_of_notMem he1, Finset.card_insert_of_notMem hm1Z, hZ']
    have hne : (fun i => σ * (η * aF i) - aG i.castSucc * (1 - yc / y i.castSucc)) ≠ 0 :=
      fun h => by
        rw [h] at hneg
        simp only [expSum, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hneg
        exact lt_irrefl _ hneg
    have := card_le_of_alternating_nat _ _ hy' hpos' hne S η
      (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) fun p hp => by
        rcases Finset.mem_insert.1 hp with rfl | hp
        · have hf : S.filter (· < e + 1) = insert (m + 1) (Z.erase z) := by
            ext q
            simp only [hS, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hq | hq | hq, hlt'⟩
              · omega
              · exact Or.inl hq
              · exact Or.inr hq
            · rintro (hq | hq)
              · exact ⟨Or.inr (Or.inl hq), hq ▸ hlt⟩
              · exact ⟨Or.inr (Or.inr hq), by have := hm1 _ hq; omega⟩
          rw [hf, Finset.card_insert_of_notMem hm1Z, pow_succ, ← hη,
            show η * (η * -1) * expSum (fun i => σ * (η * aF i) -
              aG i.castSucc * (1 - yc / y i.castSucc)) (fun i => y i.castSucc) (e + 1) =
              -(η * η) * expSum (fun i => σ * (η * aF i) -
              aG i.castSucc * (1 - yc / y i.castSucc)) (fun i => y i.castSucc) (e + 1) by ring,
            hηη]
          linarith
        rcases Finset.mem_insert.1 hp with rfl | hp
        · rw [hΔ, hΔm, mul_zero]
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 :=
          ⟨p - 1, by have := Nat.pos_of_ne_zero fun h => h0' (h ▸ hp); omega⟩
        rw [hΔ, hFdef, hF.2 _ hp, hG0 _ (Finset.mem_insert_of_mem hp), mul_zero, mul_zero,
          zero_sub, zero_sub, neg_neg]
        have hf : S.filter (· < q + 1) = (Z.erase z).filter (· < q + 1) := by
          ext r
          simp only [hS, Finset.mem_filter, Finset.mem_insert]
          have := hm1 _ hp
          constructor
          · rintro ⟨hr | hr | hr, hlt'⟩
            · omega
            · omega
            · exact ⟨hr, hlt'⟩
          · rintro ⟨hr, hlt'⟩
            exact ⟨Or.inr (Or.inr hr), hlt'⟩
        rw [hf]
        by_cases hqA : q ∈ insert 0 (Z.erase z)
        · rw [hG0 q hqA, mul_zero, mul_zero]
        have hsg := sign_before_top aG y hy hpos _ hA hG0 hGz hAz hqA
          (by have := hAz _ (Finset.mem_insert_of_mem hp); omega)
        rw [Finset.filter_insert, if_neg (Nat.not_lt_zero q)] at hsg
        have hsplit := Finset.card_filter_add_card_filter_not (s := Z.erase z) (· < q + 1)
        have hnot : (Z.erase z).filter (fun τ => ¬τ < q + 1) = (Z.erase z).filter (q < ·) :=
          Finset.filter_congr fun τ _ => by omega
        rw [hnot] at hsplit
        rw [hη, ← hsplit, pow_add]
        have hyc : 0 < yc := hpos _
        have hsq := neg_one_pow_mul_self ((Z.erase z).filter (· < q + 1)).card
        have : (-1 : ℝ) ^ ((Z.erase z).filter (· < q + 1)).card *
            (-1) ^ ((Z.erase z).filter (q < ·)).card *
            (-1) ^ ((Z.erase z).filter (· < q + 1)).card * (yc * G q) =
            yc * ((-1) ^ ((Z.erase z).filter (q < ·)).card * G q) *
            ((-1) ^ ((Z.erase z).filter (· < q + 1)).card *
              (-1) ^ ((Z.erase z).filter (· < q + 1)).card) := by ring
        rw [this, hsq, mul_one]
        exact (mul_pos hyc hsg).le
    omega
  -- combine with `σ μ ≤ 1`
  have hFe : 0 < η * F (e + 1) :=
    hFb _ (Nat.succ_pos e) fun τ hτ => by have := hm1 τ hτ; omega
  have hE : G (e + 1) - yc * G e ≤ σ * (η * F (e + 1)) := by
    rcases eq_or_lt_of_le (show m + 1 ≤ e + 1 by omega) with heq | hlt
    · have he' : e = m := by omega
      subst he'
      linarith
    · linarith [hint e hlt]
  calc (η * F z) * (G (e + 1) - yc * G e) ≤ (η * F z) * (σ * (η * F (e + 1))) :=
        mul_le_mul_of_nonneg_left hE hμ.le
    _ = (σ * (η * F z)) * (η * F (e + 1)) := by ring
    _ ≤ 1 * (η * F (e + 1)) := mul_le_mul_of_nonneg_right hσμ hFe.le
    _ = η * F (e + 1) := one_mul _

end CoefficientMass
