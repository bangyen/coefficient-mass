/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Descartes

/-!
# Signs of Exponential Sums at Natural Points

Consequences of the zero bound and of weak sign alternation for exponential
sums evaluated at natural numbers: a nonzero sum on `c` nodes vanishes at
most `c - 1` of them, and when it vanishes at exactly `c - 1` it changes sign
at each of them and nowhere else (`sign_between`).

## Theorems

* `expSum_sub`.
* `expSum_mul_left`.
* `card_add_one_le_of_zeros`.
* `expSum_ne_zero`.
* `expSum_eq_of_agree`.
* `card_filter_lt_split`.
* `sign_between`.
-/

namespace CoefficientMass

theorem expSum_sub {c : ℕ} (a b y : Fin c → ℝ) (d : ℕ) :
    expSum (fun i => a i - b i) y d = expSum a y d - expSum b y d := by
  simp only [expSum, sub_mul, Finset.sum_sub_distrib]

theorem expSum_mul_left {c : ℕ} (r : ℝ) (a y : Fin c → ℝ) (d : ℕ) :
    expSum (fun i => r * a i) y d = r * expSum a y d := by
  simp only [expSum, mul_assoc, Finset.mul_sum]

/-- A nonzero sum on `c` distinct positive nodes vanishes at most `c - 1`
natural numbers. -/
theorem card_add_one_le_of_zeros {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (ha : a ≠ 0) (S : Finset ℕ) (hS : ∀ k ∈ S, expSum a y k = 0) :
    S.card + 1 ≤ c := by
  have hsub : ((S.image (Nat.cast : ℕ → ℝ) : Finset ℝ) : Set ℝ) ⊆
      {t : ℝ | ∑ i, a i * y i ^ t = 0} := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    simp only [Set.mem_setOf_eq, Real.rpow_natCast]
    exact hS k hk
  have h1 := (Set.encard_le_encard hsub).trans (zeroBound c a y hy hpos ha)
  rw [Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective _ Nat.cast_injective] at h1
  have h2 : S.card ≤ c - 1 := by exact_mod_cast h1
  obtain ⟨i, _⟩ := Function.ne_iff.1 ha
  have := i.pos
  omega

/-- A sum on `c` nodes vanishing at `c - 1` naturals vanishes nowhere else. -/
theorem expSum_ne_zero {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (ha : a ≠ 0) (T : Finset ℕ) (hT : T.card + 1 = c)
    (hzero : ∀ τ ∈ T, expSum a y τ = 0) {t : ℕ} (ht : t ∉ T) : expSum a y t ≠ 0 := by
  intro h
  have := card_add_one_le_of_zeros a y hy hpos ha (insert t T) fun k hk => by
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact h
    · exact hzero k hk
  rw [Finset.card_insert_of_notMem ht] at this
  omega

/-- Sums that agree at `c` naturals agree everywhere. -/
theorem expSum_eq_of_agree {c : ℕ} (a b y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (S : Finset ℕ) (hS : c ≤ S.card)
    (hab : ∀ k ∈ S, expSum a y k = expSum b y k) (d : ℕ) :
    expSum a y d = expSum b y d := by
  by_cases hD : (fun i => a i - b i) = 0
  · have : a = b := funext fun i => sub_eq_zero.1 (congrFun hD i)
    rw [this]
  · have := card_add_one_le_of_zeros _ y hy hpos hD S fun k hk => by
      rw [expSum_sub, hab k hk, sub_self]
    omega

/-- Splitting the points below `t'` at `t`. -/
theorem card_filter_lt_split (T : Finset ℕ) {t t' : ℕ} (ht : t ∉ T) (hlt : t < t') :
    ((insert t (insert t' T)).filter (· < t')).card =
      ((insert t (insert t' T)).filter (· < t)).card + 1 +
        (T.filter fun τ => t < τ ∧ τ < t').card := by
  set S := insert t (insert t' T)
  rw [← Finset.card_filter_add_card_filter_not (p := (· < t)), Finset.filter_filter,
    Finset.filter_filter, add_assoc]
  congr 1
  · refine congrArg Finset.card (Finset.filter_congr fun q _ => ?_)
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans hlt, h⟩
  · have hE : S.filter (fun q => q < t' ∧ ¬q < t) =
        insert t (T.filter fun τ => t < τ ∧ τ < t') := by
      ext q
      simp only [S, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq | hq | hq, h1, h2⟩
        · exact Or.inl hq
        · omega
        · rcases eq_or_ne q t with rfl | hne
          · exact Or.inl rfl
          · exact Or.inr ⟨hq, by omega, h1⟩
      · rintro (rfl | ⟨hq, h1, h2⟩)
        · exact ⟨Or.inl rfl, hlt, lt_irrefl _⟩
        · exact ⟨Or.inr (Or.inr hq), h2, by omega⟩
    rw [hE, Finset.card_insert_of_notMem fun h => ht (Finset.mem_filter.1 h).1, add_comm]

/-- A sum on `c` nodes with `c - 1` zeros changes sign exactly at them:
between two other naturals it flips once for each zero in between. -/
theorem sign_between {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (ha : a ≠ 0) (T : Finset ℕ) (hT : T.card + 1 = c)
    (hzero : ∀ τ ∈ T, expSum a y τ = 0) {t t' : ℕ} (ht : t ∉ T) (ht' : t' ∉ T)
    (hlt : t < t') :
    0 < (-1) ^ (T.filter fun τ => t < τ ∧ τ < t').card * (expSum a y t * expSum a y t') := by
  have hf := expSum_ne_zero a y hy hpos ha T hT hzero ht
  have hf' := expSum_ne_zero a y hy hpos ha T hT hzero ht'
  by_contra hle
  push_neg at hle
  set b := (T.filter fun τ => t < τ ∧ τ < t').card
  set S := insert t (insert t' T) with hS
  set k := (S.filter (· < t)).card
  have hk' := card_filter_lt_split T ht hlt
  have hcard : S.card = c + 1 := by
    rw [hS, Finset.card_insert_of_notMem (by
      rw [Finset.mem_insert]; exact fun h => h.elim (fun h => hlt.ne h) ht),
      Finset.card_insert_of_notMem ht', hT]
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have := card_le_of_alternating_nat a y hy hpos ha S ((-1) ^ k * expSum a y t)
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hf) fun p hp => by
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have : 0 ≤ ((-1) ^ k * (-1) ^ k) * (expSum a y p * expSum a y p) :=
          mul_nonneg (by rw [hsq]; exact zero_le_one) (mul_self_nonneg _)
        linarith
      rcases Finset.mem_insert.1 hp with rfl | hp
      · rw [hk', pow_add, pow_add, pow_one]
        have : 0 ≤ ((-1) ^ k * (-1) ^ k) *
            -((-1) ^ b * (expSum a y t * expSum a y p)) := by
          rw [hsq, one_mul]
          linarith
        linarith
      · rw [hzero p hp, mul_zero]
  omega

end CoefficientMass
