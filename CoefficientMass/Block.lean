/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.BlockProd
import CoefficientMass.LongDiag
import CoefficientMass.SecondRow

/-!
# The Exempted Block `[2, k]`

This module proves Lemma 6.21 of `coefficient-mass-rows.tex`.  Every polynomial admissible for
`μ_r([1, k], L) = ν_{k+1}(n - 1)` is admissible for `μ_r([2, k], L)`.  For the second bound take
`p = r_Y` from Lemma 3.1 with `A_k(p) < ν_k(n) + ε` and `q(s) = r_{[2,k]}(s) p(s - 1)/p(-1)`;
since `|r_{[2,k]}(s)| r^{-s} = ω_k(s - 1)/(kr)` for `s ≥ 2` and `|r_{[2,k]}(1)| = 1/k`,
`Φ_r(q) = (1 + A_k(p))/(kr p(-1))` with `p(-1) ≥ 1`.

## Definitions

* `Block`.

## Theorems

* `muR_mono_set`.
* `one_le_eval_neg_one`.
* `muR_block_le_prefix`.
* `muR_block_le`.
* `block`.
-/

open Polynomial

namespace CoefficientMass

/-- Lemma 6.21 of `coefficient-mass-rows.tex`: for `r > 1`, `n, k ≥ 2` and `L = n + k - 1`,
`μ_r([2, k], L) ≤ min(ν_{k+1}(n - 1), (1 + ν_k(n))/(kr))`, with equality in the first bound if
some minimizer vanishes at `1`; and if `μ_r([2, k], L) > M = max_{i ≤ k} ν_i(n)` then
`ν_{k+1}(n - 1) > M` and `k < (β_r(n) + 1)/r`. -/
def Block : Prop :=
  ∀ r : ℝ, 1 < r → ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
    muR r (Finset.Icc 2 k) (n + k - 1) ≤ nuR r (k + 1) (n - 1) ∧
    muR r (Finset.Icc 2 k) (n + k - 1) ≤ (1 + nuR r k n) / (k * r) ∧
    ((∃ q : ℝ[X], q.degree < ↑(n + k - 1) ∧ q.eval 0 = 1 ∧
        (∀ s ∈ Finset.Icc 2 k, q.eval (s : ℝ) = 0) ∧
        rowPhi r q = muR r (Finset.Icc 2 k) (n + k - 1) ∧ q.eval 1 = 0) →
      muR r (Finset.Icc 2 k) (n + k - 1) = nuR r (k + 1) (n - 1)) ∧
    ((Finset.Icc 1 k).fold max 0 (fun i => nuR r i n) < muR r (Finset.Icc 2 k) (n + k - 1) →
      (Finset.Icc 1 k).fold max 0 (fun i => nuR r i n) < nuR r (k + 1) (n - 1) ∧
        (k : ℝ) < (rowValue r n 1 + 1) / r)

/-- `μ_r(S, L) ≤ μ_r(T, L)` for `S ⊆ T`, `0 ∉ T` and `|T| < L`. -/
theorem muR_mono_set {r : ℝ} (hr : 1 < r) {S T : Finset ℕ} (hST : S ⊆ T) {L : ℕ} (h0 : 0 ∉ T)
    (hT : T.card < L) : muR r S L ≤ muR r T L := by
  obtain ⟨h1, h2, h3⟩ := confPolyP_admissible (L := L) h0 hT
  haveI : Nonempty {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ T, q.eval (s : ℝ) = 0} :=
    ⟨⟨_, h1, h2, h3⟩⟩
  unfold muR
  refine le_ciInf fun q => ciInf_le ⟨0, ?_⟩ (⟨q.1, q.2.1, q.2.2.1, fun s hs => q.2.2.2 s (hST hs)⟩ :
    {q : ℝ[X] // q.degree < L ∧ q.eval 0 = 1 ∧ ∀ s ∈ S, q.eval (s : ℝ) = 0})
  rintro _ ⟨q, rfl⟩
  exact tsum_nonneg fun _ => by positivity

/-- `r_Y(-1) = ∏_{y ∈ Y} (1 + 1/y) ≥ 1`. -/
theorem one_le_eval_neg_one (Y : Finset ℕ) : 1 ≤ (confPolyP Y).eval (-1) := by
  rw [confPolyP, eval_prod]
  calc (1 : ℝ) = ∏ _y ∈ Y, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ y ∈ Y, (C (-(1 / (y : ℝ))) * X + C 1).eval (-1) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun y _ => by
          rw [eval_add, eval_mul, eval_C, eval_X, eval_C]
          have : 0 ≤ 1 / (y : ℝ) := by positivity
          linarith

/-- `μ_r([2, k], n + k - 1) ≤ ν_{k+1}(n - 1)`. -/
theorem muR_block_le_prefix {r : ℝ} (hr : 1 < r) {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    muR r (Finset.Icc 2 k) (n + k - 1) ≤ nuR r (k + 1) (n - 1) := by
  have e := muR_prefix hr (show 1 ≤ k + 1 by omega) (show 1 ≤ n - 1 by omega)
  rw [Nat.add_sub_cancel, show n - 1 + k = n + k - 1 by omega] at e
  rw [← e]
  exact muR_mono_set hr (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    (fun h => by have := (Finset.mem_Icc.1 h).1; omega) (by rw [Nat.card_Icc]; omega)

end CoefficientMass
