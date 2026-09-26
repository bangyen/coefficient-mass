/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.CrossD
import CoefficientMass.RowFar

/-!
# Every Row Against the Top Row

This module proves Theorem 5.3 of `coefficient-mass-rows.tex`.  With `λ = max(1, 1/(r - 1))`,
induction on `|S|` along its largest element `σ` gives
`μ_{r,D}(S, |S| + n) ≤ λ^{|S|} μ_{r,D}(∅, n)` for `D ≥ |S| + n + max S`: a vertex minimizer `W`
for `S \ {σ}` (Lemma 5.1), the truncated crossing with `ins(W, h)` (Theorem 4.3) and Lemma 5.2
bound one step.  Letting `D → ∞` gives `μ_r(S, |S| + n) ≤ λ^{|S|} μ_r(∅, n)`, hence
`V_r(L, k) ≥ min(1, r - 1)^{k - 1} β_r(L - k + 1)`, with equality for `r ≥ 2`.

## Definitions

* `AllRowsTwo`.

## Theorems

* `sum_range_eq_phiD`.
* `min_mul_max_inv`.
* `muRD_le_pow`.
* `muRD_empty_le`.
* `muR_le_pow`.
* `allRowsTwo`.
-/

open Polynomial

namespace CoefficientMass

/-- Theorem 5.3 of `coefficient-mass-rows.tex`: for `r > 1`, `a = 1/(r - 1)`, `n ≥ 1` and
finite `S ⊂ ℕ_{>0}`, `μ_r(S, |S| + n) ≤ max(1, a)^{|S|} μ_r(∅, n)` (and `μ_r(∅, n) = 1/β_r(n)`);
consequently `V_r(L, k) ≥ min(1, r - 1)^{k - 1} β_r(L - k + 1)` for `1 ≤ k ≤ L`, and
`V_r(L, k) = β_r(L - k + 1)` for `r ≥ 2`. -/
def AllRowsTwo : Prop :=
  ∀ r : ℝ, 1 < r →
    (∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, 0 ∉ S →
      muR r S (S.card + n) ≤ max 1 (1 / (r - 1)) ^ S.card * muR r ∅ n) ∧
    (∀ L k : ℕ, 1 ≤ k → k ≤ L →
      min 1 (r - 1) ^ (k - 1) * rowValue r (L - k + 1) 1 ≤ rowValue r L k) ∧
    (2 ≤ r → ∀ L k : ℕ, 1 ≤ k → k ≤ L → rowValue r L k = rowValue r (L - k + 1) 1)

theorem sum_range_eq_phiD (r : ℝ) (D : ℕ) (q : ℝ[X]) :
    ∑ d ∈ Finset.range D, |q.eval ((d + 1 : ℕ) : ℝ)| * (1 / r) ^ (d + 1) = phiD r D q := by
  rw [phiD, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun s : ℕ => |q.eval (s : ℝ)| * (1 / r) ^ s),
    zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem min_mul_max_inv {r : ℝ} (hr : 1 < r) : min 1 (r - 1) * max 1 (1 / (r - 1)) = 1 := by
  have hr1 : 0 < r - 1 := by linarith
  rcases le_total r 2 with h2 | h2
  · rw [min_eq_right (by linarith), max_eq_right (one_le_one_div hr1 (by linarith)),
      mul_one_div_cancel hr1.ne']
  · rw [min_eq_left (by linarith), max_eq_left ((div_le_one hr1).2 (by linarith)), one_mul]

/-- The truncated form of Theorem 5.3 of `coefficient-mass-rows.tex`. -/
theorem muRD_le_pow {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) (S : Finset ℕ) :
    0 ∉ S → ∀ D : ℕ, S.card + n + S.sup id ≤ D →
      muRD r D S (S.card + n) ≤ max 1 (1 / (r - 1)) ^ S.card * muRD r D ∅ n := by
  induction S using Finset.induction_on_max with
  | h0 => intro _ D _; simp only [Finset.card_empty, zero_add, pow_zero, one_mul, le_refl]
  | step σ T hlt ih =>
    intro h0 D hD
    have hσT : σ ∉ T := fun h => lt_irrefl _ (hlt σ h)
    have hσ0 : 0 < σ := Nat.pos_of_ne_zero fun h => h0 (h ▸ Finset.mem_insert_self _ _)
    have hT0 : 0 ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    have hcard : (insert σ T).card = T.card + 1 := Finset.card_insert_of_notMem hσT
    set t := T.sup id
    have hTt : ∀ x ∈ T, x ≤ t := fun x hx => Finset.le_sup (f := id) hx
    have htσ : t < σ := (Finset.sup_lt_iff hσ0).2 fun x hx => hlt x hx
    have hsup : σ ≤ (insert σ T).sup id := Finset.le_sup (f := id) (Finset.mem_insert_self _ _)
    rw [hcard] at hD ⊢
    obtain ⟨W, hTW, hWD, hWc, hopt⟩ := truncVertex r hr T (T.card + n) D hT0 (by omega)
      (by omega)
    have h0W : 0 ∉ W := fun h => by have := (Finset.mem_Icc.1 (hWD h)).1; omega
    obtain ⟨hth, hhW, -⟩ := firstGap_spec t W
    have hcross := muRD_insert_le hr D t W T σ h0W hTW hTt htσ
    rw [show W.card + 2 = T.card + 1 + n by omega] at hcross
    have hopt' : phiD r D (confPolyP W) = muRD r D T (W.card + 1) := by rw [hWc]; exact hopt
    have hmax := (optInsMax r hr D T W (firstGap t W) h0W hTW (by omega) hhW
      (fun x hx => (hTt x hx).trans_lt hth) hopt').1
    have hlam : 1 ≤ max 1 (1 / (r - 1)) := le_max_left _ _
    have hφ : 0 ≤ phiD r D (confPolyP W) := Finset.sum_nonneg fun _ _ => by positivity
    have hih := ih hT0 D (by omega)
    rw [← hopt] at hih
    calc muRD r D (insert σ T) (T.card + 1 + n)
        ≤ max 1 (1 / (r - 1)) * phiD r D (confPolyP W) :=
          hcross.trans (max_le (le_mul_of_one_le_left hφ hlam) hmax)
      _ ≤ max 1 (1 / (r - 1)) * (max 1 (1 / (r - 1)) ^ T.card * muRD r D ∅ n) :=
          mul_le_mul_of_nonneg_left hih (zero_le_one.trans hlam)
      _ = max 1 (1 / (r - 1)) ^ (T.card + 1) * muRD r D ∅ n := by ring

/-- `μ_{r,D}(∅, n) ≤ μ_r(∅, n)`. -/
theorem muRD_empty_le {r : ℝ} (hr : 1 < r) (D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    muRD r D ∅ n ≤ muR r ∅ n := by
  haveI : Nonempty {q : ℝ[X] // q.degree < n ∧ q.eval 0 = 1 ∧ ∀ s ∈ (∅ : Finset ℕ),
      q.eval (s : ℝ) = 0} :=
    ⟨⟨1, by rw [degree_one]; exact_mod_cast hn, eval_one, fun s hs => absurd hs
      (Finset.notMem_empty s)⟩⟩
  refine le_ciInf fun q => ?_
  refine (ciInf_le ⟨0, by
    rintro _ ⟨q', rfl⟩
    exact Finset.sum_nonneg fun _ _ => by positivity⟩ q).trans ?_
  rw [← sum_range_eq_phiD]
  exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_rowPhi hr q.1)

theorem muR_le_pow {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) (S : Finset ℕ) (h0 : 0 ∉ S) :
    muR r S (S.card + n) ≤ max 1 (1 / (r - 1)) ^ S.card * muR r ∅ n := by
  obtain ⟨hc, hc0, hcS⟩ := confPolyP_admissible (L := S.card + n) h0 (by omega)
  haveI : Nonempty {q : ℝ[X] // q.degree < ↑(S.card + n) ∧ q.eval 0 = 1 ∧
      ∀ s ∈ S, q.eval (s : ℝ) = 0} := ⟨⟨_, hc, hc0, hcS⟩⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨M₀, hM₀⟩ := exists_trunc_ge hr S (S.card + n) hε
  set D := max M₀ (S.card + n + S.sup id)
  have hμD : muR r S (S.card + n) - ε ≤ muRD r D S (S.card + n) := le_ciInf fun q => by
    obtain ⟨q, hq, hq0, hqS⟩ := q
    have := hM₀ D (le_max_left _ _) q hq hq0 hqS
    rwa [sum_range_eq_phiD] at this
  have hpow := muRD_le_pow hr hn S h0 D (le_max_right _ _)
  have hemp := mul_le_mul_of_nonneg_left (muRD_empty_le hr D hn)
    (pow_nonneg (zero_le_one.trans (le_max_left 1 (1 / (r - 1)))) S.card)
  linarith

theorem allRowsTwo : AllRowsTwo := by
  intro r hr
  have hpart1 : ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, 0 ∉ S →
      muR r S (S.card + n) ≤ max 1 (1 / (r - 1)) ^ S.card * muR r ∅ n :=
    fun n hn S h0 => muR_le_pow hr hn S h0
  have hpart2 : ∀ L k : ℕ, 1 ≤ k → k ≤ L →
      min 1 (r - 1) ^ (k - 1) * rowValue r (L - k + 1) 1 ≤ rowValue r L k := by
    intro L k hk hkL
    set n := L - k + 1
    rw [(rowValueDual r hr).1 L k hk hkL, (rowValueDual r hr).2 n (by omega)]
    haveI : Nonempty {S : Finset ℕ // 0 ∉ S ∧ S.card + 1 = k} :=
      ⟨⟨Finset.Icc 1 (k - 1), fun h => by have := (Finset.mem_Icc.1 h).1; omega,
        by rw [Nat.card_Icc]; omega⟩⟩
    refine le_ciInf fun S => ?_
    obtain ⟨S, hS0, hSk⟩ := S
    have hL : L = S.card + n := by omega
    have hμS := muR_pos hr hS0 (show S.card < S.card + n by omega)
    have hμ0 := muR_pos hr (Finset.notMem_empty 0) (show (∅ : Finset ℕ).card < n by
      rw [Finset.card_empty]; omega)
    have hμ := hpart1 n (by omega) S hS0
    rw [hL, mul_one_div, div_le_div_iff₀ hμ0 hμS, one_mul]
    have hm : 0 ≤ min 1 (r - 1) ^ (k - 1) := pow_nonneg (le_min zero_le_one (by linarith)) _
    have hk1 : S.card = k - 1 := by omega
    calc min 1 (r - 1) ^ (k - 1) * muR r S (S.card + n)
        ≤ min 1 (r - 1) ^ (k - 1) * (max 1 (1 / (r - 1)) ^ S.card * muR r ∅ n) :=
          mul_le_mul_of_nonneg_left hμ hm
      _ = muR r ∅ n := by rw [hk1, ← mul_assoc, ← mul_pow, min_mul_max_inv hr, one_pow, one_mul]
  refine ⟨hpart1, hpart2, fun h2 L k hk hkL => le_antisymm (rowValueTop r hr L k hk hkL) ?_⟩
  have := hpart2 L k hk hkL
  rwa [min_eq_left (by linarith : (1 : ℝ) ≤ r - 1), one_pow, one_mul] at this

end CoefficientMass
