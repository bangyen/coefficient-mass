/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Certificate
import CoefficientMass.Consecutive
import CoefficientMass.DisplacedTail

/-!
# The Displaced-Zero Tail Bound

This module proves Theorem 2.2 of `coefficient-mass.tex` by induction on the
number of nodes.  With no displaced zeros it is Lemma 2.1 with the factors
beyond the leading run dropped, each being at most one because the nodes are
at most `1/2`.  Otherwise the largest zero and the largest node are removed,
which does not decrease the tail (`tsum_le_of_displaced`) and keeps the
leading run.

## Theorems

* `tailBound_consecutive`.
* `summable_tail`.
* `nodeProduct_castSucc`.
* `tailBound`.
-/

namespace CoefficientMass

/-- Theorem 2.2 with no displaced zeros: the zero set is `{1, …, c - 1}`. -/
theorem tailBound_consecutive {c : ℕ} (a y : Fin c → ℝ) (ℓ : ℕ) (hmono : StrictMono y)
    (hpos : ∀ i, 0 < y i) (hhalf : ∀ i, y i ≤ 1 / 2) (ha : IsCertificate a y (Finset.Ioo 0 c)) :
    Summable (fun d => |expSum a y (d + 1)|) ∧
      ∑' d, |expSum a y (d + 1)| ≤ nodeProduct y ℓ := by
  have h := consecutiveTail c a y hmono hpos (fun i => by linarith [hhalf i]) ha
  refine ⟨h.summable, ?_⟩
  have hf : ∀ i, 0 ≤ y i / (1 - y i) ∧ y i / (1 - y i) ≤ 1 := fun i => by
    have h1 : 0 < 1 - y i := by linarith [hhalf i]
    exact ⟨div_nonneg (hpos i).le h1.le, (div_le_one h1).2 (by linarith [hhalf i])⟩
  rw [h.tsum_eq, nodeProduct,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin c => i.val ≤ ℓ)]
  exact mul_le_of_le_one_right (Finset.prod_nonneg fun i _ => (hf i).1)
    (Finset.prod_le_one (fun i _ => (hf i).1) fun i _ => (hf i).2)

theorem summable_tail {c : ℕ} (a y : Fin c → ℝ) (hpos : ∀ i, 0 < y i) (hy1 : ∀ i, y i < 1) :
    Summable fun d => |expSum a y (d + 1)| := by
  have h := hasSum_sum fun i (_ : i ∈ Finset.univ) =>
    (hasSum_geometric_of_lt_one (hpos i).le (hy1 i)).mul_left (a i * y i)
  refine (h.summable.congr fun d => ?_).abs
  rw [expSum]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_succ']; ring

theorem nodeProduct_castSucc {n : ℕ} (y : Fin (n + 1) → ℝ) {ℓ : ℕ} (hℓ : ℓ < n) :
    nodeProduct (fun i => y i.castSucc) ℓ = nodeProduct y ℓ := by
  rw [nodeProduct, nodeProduct, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [if_neg (by omega), mul_one]

/-- Theorem 2.2 (displaced-zero tail bound). -/
theorem tailBound : TailBound := by
  intro c
  induction c with
  | zero =>
    intro a y Z ℓ _ _ _ _ _ _ ha
    have h1 := ha.1
    simp only [expSum, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 zero_ne_one
  | succ n ih =>
    intro a y Z ℓ hmono hpos hhalf h0 hcard hℓ ha
    rw [Nat.add_sub_cancel] at hcard
    refine ⟨summable_tail a y hpos fun i => by linarith [hhalf i], ?_⟩
    by_cases hZ : Z = Finset.Ioo 0 (n + 1)
    · subst hZ
      exact (tailBound_consecutive a y ℓ hmono hpos hhalf ha).2
    have hIoo : ∀ τ, τ ∈ Finset.Ioo 0 (n + 1) ↔ 1 ≤ τ ∧ τ ≤ n := fun τ => by
      rw [Finset.mem_Ioo]
      omega
    have hIoocard : (Finset.Ioo 0 (n + 1)).card = n := by rw [Nat.card_Ioo]; omega
    have hne : Z.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      refine hZ (Finset.eq_empty_of_forall_notMem fun τ hτ => ?_).symm
      rw [Finset.card_empty] at hcard
      have := (hIoo τ).1 hτ
      omega
    set z := Z.max' hne
    have hz : z ∈ Z := Z.max'_mem hne
    have hzmax : ∀ τ ∈ Z, τ ≤ z := fun τ hτ => Z.le_max' τ hτ
    have hzn : n + 1 ≤ z := by
      by_contra hlt
      push_neg at hlt
      refine hZ (Finset.eq_of_subset_of_card_le (fun τ hτ => (hIoo τ).2 ⟨?_, ?_⟩) ?_)
      · exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hτ)
      · have := hzmax τ hτ
        omega
      · rw [hIoocard, hcard]
    have hℓn : ℓ < n := by
      by_contra hle
      push_neg at hle
      refine hZ (Finset.eq_of_subset_of_card_le (fun τ hτ => hℓ ?_) ?_).symm
      · have := (hIoo τ).1 hτ
        exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · rw [hIoocard, hcard]
    set Z' := Z.erase z
    have h0' : 0 ∉ Z' := fun h => h0 (Finset.mem_of_mem_erase h)
    have hZ'card : Z'.card = n - 1 := by rw [Finset.card_erase_of_mem hz, hcard]
    have hℓ' : Finset.Icc 1 ℓ ⊆ Z' := fun τ hτ => by
      have := Finset.mem_Icc.1 hτ
      exact Finset.mem_erase.2 ⟨by omega, hℓ hτ⟩
    have hmono' : StrictMono fun i : Fin n => y i.castSucc :=
      fun i j h => hmono (Fin.castSucc_lt_castSucc_iff.2 h)
    obtain ⟨aF, hF⟩ := exists_certificate zeroBound (fun i : Fin n => y i.castSucc)
      hmono'.injective (fun i => hpos _) Z' h0' (by
        have := Finset.card_pos.2 ⟨z, hz⟩
        omega)
    obtain ⟨hFs, hFb⟩ := ih aF (fun i => y i.castSucc) Z' ℓ hmono' (fun i => hpos _)
      (fun i => hhalf _) h0' hZ'card hℓ' hF
    calc ∑' d, |expSum a y (d + 1)|
        ≤ ∑' d, |expSum aF (fun i => y i.castSucc) (d + 1)| :=
          tsum_le_of_displaced y hmono hpos hhalf Z hz hzmax h0 hcard a ha aF hF hFs
      _ ≤ nodeProduct (fun i => y i.castSucc) ℓ := hFb
      _ = nodeProduct y ℓ := nodeProduct_castSucc y hℓn

end CoefficientMass
