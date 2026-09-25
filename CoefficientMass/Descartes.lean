/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ZeroBound
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Finset.Sort

/-!
# Weak Sign Alternation

A nonzero exponential sum on `n` distinct nodes cannot weakly alternate in
sign at more than `n` points: if `σ (-1)^k f(P_k) ≥ 0` at `P_0 < ⋯ < P_{N-1}`
then `N ≤ n`.  Divide by one exponential; by the mean value theorem the
derivative, a sum on one fewer node, weakly alternates at a point inside each
of the `N - 1` gaps.  This replaces the paper's count of zeros with
multiplicity: a zero where the sign does not change is a weak alternation on
both sides.

## Theorems

* `card_le_of_alternating`.
* `card_filter_lt_orderEmbOfFin`.
* `expSum_eq_sum_exp`.
* `card_le_of_alternating_nat`.
-/

namespace CoefficientMass

/-- Weak sign alternation in exponential form. -/
theorem card_le_of_alternating {ι : Type*} (s : Finset ι) :
    ∀ a lam : ι → ℝ, Set.InjOn lam s → (∃ i ∈ s, a i ≠ 0) →
      ∀ (n : ℕ) (P : Fin n → ℝ), StrictMono P → ∀ σ : ℝ, σ ≠ 0 →
        (∀ k : Fin n, 0 ≤ σ * (-1) ^ (k : ℕ) * ∑ i ∈ s, a i * Real.exp (lam i * P k)) →
          n ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a lam _ h
    obtain ⟨i, hi, _⟩ := h
    exact absurd hi (Finset.notMem_empty i)
  | insert j s hj ih =>
    intro a lam hinj h n P hP σ hσ htemp
    rw [Finset.card_insert_of_notMem hj]
    by_cases hs : ∃ i ∈ s, a i ≠ 0
    swap
    · -- a single exponential has a strict sign, so it alternates at most once
      push_neg at hs
      have haj : a j ≠ 0 := by
        obtain ⟨i, hi, hai⟩ := h
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hai
        · exact absurd (hs i hi) hai
      by_contra hlt
      push_neg at hlt
      have hf : ∀ t, ∑ i ∈ insert j s, a i * Real.exp (lam i * t) =
          a j * Real.exp (lam j * t) := fun t => by
        rw [Finset.sum_insert hj, Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_mul],
          add_zero]
      have h0 := htemp ⟨0, by omega⟩
      have h1 := htemp ⟨1, by omega⟩
      rw [hf] at h0 h1
      simp only [pow_zero, pow_one, mul_one] at h0 h1
      have he0 := Real.exp_pos (lam j * P ⟨0, by omega⟩)
      have he1 := Real.exp_pos (lam j * P ⟨1, by omega⟩)
      rcases lt_or_gt_of_ne (mul_ne_zero hσ haj) with hneg | hpos
      · nlinarith [mul_neg_of_neg_of_pos hneg he0]
      · nlinarith [mul_pos hpos he1]
    rcases n with _ | n
    · exact Nat.zero_le _
    -- divide by `e^{λ_j t}`
    set g : ℝ → ℝ := fun t => a j + ∑ i ∈ s, a i * Real.exp ((lam i - lam j) * t) with hg
    set g' : ℝ → ℝ :=
      fun t => ∑ i ∈ s, a i * (lam i - lam j) * Real.exp ((lam i - lam j) * t)
    have hderiv : ∀ t, HasDerivAt g (g' t) t := fun t => by
      refine ((HasDerivAt.fun_sum fun i _ =>
        (((hasDerivAt_id t).const_mul (lam i - lam j)).exp.const_mul (a i))).const_add
          (a j)).congr_deriv ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [id]
      ring
    have hfg : ∀ t, ∑ i ∈ insert j s, a i * Real.exp (lam i * t) =
        Real.exp (lam j * t) * g t := fun t => by
      have he : ∀ i, Real.exp (lam i * t) =
          Real.exp (lam j * t) * Real.exp ((lam i - lam j) * t) :=
        fun i => by rw [← Real.exp_add]; ring_nf
      simp only [hg]
      rw [Finset.sum_insert hj, he j, sub_self, zero_mul, Real.exp_zero, mul_one,
        Finset.sum_congr rfl fun i _ => by rw [he i, mul_left_comm], ← Finset.mul_sum,
        mul_comm (a j), ← mul_add]
    have htg : ∀ k : Fin (n + 1), 0 ≤ σ * (-1) ^ (k : ℕ) * g (P k) := fun k => by
      have h1 := htemp k
      rw [hfg] at h1
      have h2 : 0 ≤ Real.exp (lam j * P k) * (σ * (-1) ^ (k : ℕ) * g (P k)) := by linarith
      exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1 h2
    -- the mean value theorem in each gap
    have hQ : ∀ k : Fin n, ∃ q ∈ Set.Ioo (P k.castSucc) (P k.succ),
        g' q = (g (P k.succ) - g (P k.castSucc)) / (P k.succ - P k.castSucc) := fun k =>
      exists_hasDerivAt_eq_slope g g' (hP ((Fin.castSucc_lt_succ (i := k))))
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt) (fun x _ => hderiv x)
    choose Q hQmem hQeq using hQ
    have hQmono : StrictMono Q := fun k k' hkk' =>
      (hQmem k).2.trans_le
        ((hP.monotone (Fin.succ_le_castSucc_iff.2 hkk')).trans (hQmem k').1.le)
    have htg' : ∀ k : Fin n, 0 ≤ -σ * (-1) ^ (k : ℕ) * g' (Q k) := fun k => by
      rw [hQeq k, mul_div_assoc']
      have h1 := htg k.succ
      have h2 := htg k.castSucc
      rw [Fin.val_succ, pow_succ] at h1
      rw [Fin.val_castSucc] at h2
      exact div_nonneg (by linarith) (sub_pos.2 (hP ((Fin.castSucc_lt_succ (i := k))))).le
    have hn := ih (fun i => a i * (lam i - lam j)) (fun i => lam i - lam j)
      (fun x hx y hy hxy => hinj (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
        (sub_left_injective hxy)) (by
        obtain ⟨i, hi, hai⟩ := hs
        refine ⟨i, hi, mul_ne_zero hai (sub_ne_zero.2 fun he => ?_)⟩
        exact hj (hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self j s) he ▸ hi))
      n Q hQmono (-σ) (neg_ne_zero.2 hσ) htg'
    omega

/-- The position of the `k`-th smallest element of `S` among the elements of `S`. -/
theorem card_filter_lt_orderEmbOfFin (S : Finset ℕ) (k : Fin S.card) :
    (S.filter (· < S.orderEmbOfFin rfl k)).card = k := by
  have h := congrArg (fun T => (T.filter (· < S.orderEmbOfFin rfl k)).card)
    (Finset.map_orderEmbOfFin_univ S rfl)
  simp only at h
  rw [← h, Finset.filter_map, Finset.card_map]
  have hI : Finset.univ.filter ((· < S.orderEmbOfFin rfl k) ∘
      (S.orderEmbOfFin rfl).toEmbedding) = Finset.Iio k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Finset.mem_Iio]
    exact (S.orderEmbOfFin rfl).lt_iff_lt
  rw [hI, Fin.card_Iio]

theorem expSum_eq_sum_exp {c : ℕ} (a y : Fin c → ℝ) (hpos : ∀ i, 0 < y i) (d : ℕ) :
    expSum a y d = ∑ i ∈ Finset.univ, a i * Real.exp (Real.log (y i) * d) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log (hpos i)]

/-- Weak sign alternation at natural points, the index of `p` being the number
of points below it. -/
theorem card_le_of_alternating_nat {c : ℕ} (a y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (ha : a ≠ 0) (S : Finset ℕ) (σ : ℝ) (hσ : σ ≠ 0)
    (h : ∀ p ∈ S, 0 ≤ σ * (-1) ^ (S.filter (· < p)).card * expSum a y p) :
    S.card ≤ c := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have := card_le_of_alternating Finset.univ a (fun i => Real.log (y i))
    (fun x _ z _ hxz => hy (Real.log_injOn_pos (hpos x) (hpos z) hxz))
    ⟨i, Finset.mem_univ i, hi⟩ S.card (fun k => (S.orderEmbOfFin rfl k : ℝ))
    (fun k k' hkk' => Nat.cast_lt.2 ((S.orderEmbOfFin rfl).strictMono hkk')) σ hσ
    (fun k => by
      have hk := h _ (Finset.orderEmbOfFin_mem S rfl k)
      rw [card_filter_lt_orderEmbOfFin, expSum_eq_sum_exp a y hpos] at hk
      exact hk)
  rwa [Finset.card_univ, Fintype.card_fin] at this

end CoefficientMass
