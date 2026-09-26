/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.FarZeros
import CoefficientMass.RowMono

/-!
# The Far Step

This module proves the far step in the proof of Theorem 6.19 of
`coefficient-mass-rows.tex`.  If `q` is admissible for `μ_r(N, n + |N|)`, `N ⊂ S`, `|S| = m` and
`Δ_{q,m-|N|}(t) ≤ 0` with `S \ N ⊂ [t, ∞)`, then Lemma 6.18(b) gives
`μ_r(S, n + m) ≤ Φ_r(q r_{S \ N}) ≤ Φ_r(q)`.  Lemma 6.10 also gives
`V_r(n + m - 1, m) ≤ V_r(n + j, j + 1) ≤ 1/μ_r(N, n + j)` for `|N| = j < m`.

## Theorems

* `muR_le_of_far`.
* `rowValue_diag_anti`.
* `rowValue_le_muR`.
-/

open Polynomial

namespace CoefficientMass

/-- `μ_r(S, n + m) ≤ Φ_r(q)` when `q` is admissible for `N ⊂ S`, `|S| = m`, and the positions
of `S \ N` lie past a `t > 0` with `Δ_{q,m-|N|}(t) ≤ 0`. -/
theorem muR_le_of_far {r : ℝ} (hr : 1 < r) {n m : ℕ} {S N : Finset ℕ} {q : ℝ[X]}
    (hNS : N ⊆ S) (hS : S.card = m) (hNm : N.card < m) (hq : q.degree < n + N.card)
    (hq0 : q.eval 0 = 1) (hqN : ∀ s ∈ N, q.eval (s : ℝ) = 0) {t : ℝ} (ht : 0 < t)
    (hΔ : deltaQ r q (m - N.card) t ≤ 0) (hU : ∀ v ∈ S \ N, t ≤ v) :
    muR r S (n + m) ≤ rowPhi r q := by
  have hqne : q ≠ 0 := fun h => by rw [h, eval_zero] at hq0; exact zero_ne_one hq0
  have hUc : (S \ N).card = m - N.card := by rw [Finset.card_sdiff_of_subset hNS, hS]
  have hqn : q.natDegree < n + N.card := by
    rw [degree_eq_natDegree hqne] at hq
    exact_mod_cast hq
  have hdeg : (q * confPolyP (S \ N)).natDegree < n + m :=
    (natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_confPolyP _) _)).trans_lt (by omega)
  refine (ciInf_le ⟨0, ?_⟩ (⟨q * confPolyP (S \ N),
    degree_le_natDegree.trans_lt (by exact_mod_cast hdeg), ?_, fun s hs => ?_⟩ :
      {p : ℝ[X] // p.degree < ↑(n + m) ∧ p.eval 0 = 1 ∧ ∀ s ∈ S, p.eval (s : ℝ) = 0})).trans
    (rowPhi_mul_confPolyP_le hr (by omega) q ht hΔ hUc.le hU)
  · rintro _ ⟨p, rfl⟩
    exact tsum_nonneg fun _ => by positivity
  · rw [eval_mul, hq0, one_mul, confPolyP, eval_prod]
    exact Finset.prod_eq_one fun z _ => by
      rw [eval_add, eval_mul, eval_C, eval_X, eval_C, mul_zero, zero_add]
  · rw [eval_mul]
    by_cases hsN : s ∈ N
    · rw [hqN s hsN, zero_mul]
    · have hsU : s ∈ S \ N := Finset.mem_sdiff.2 ⟨hs, hsN⟩
      have : t ≤ s := hU s hsU
      rw [confPolyP_eval_mem hsU (by rintro rfl; push_cast at this; linarith), mul_zero]

/-- `V_r(n + k - 1, k)` does not increase in `k ≥ 1`. -/
theorem rowValue_diag_anti {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) {j k : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) : rowValue r (n + k - 1) k ≤ rowValue r (n + j - 1) j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ((rowMono r hr).2 n k hn (by omega)).trans ih

/-- `V_r(n + |N|, |N| + 1) ≤ 1/μ_r(N, n + |N|)`. -/
theorem rowValue_le_muR {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 1 ≤ n) {N : Finset ℕ} (h0 : 0 ∉ N) :
    rowValue r (n + N.card) (N.card + 1) ≤ 1 / muR r N (n + N.card) := by
  rw [(rowValueDual r hr).1 _ _ (by omega) (by omega)]
  exact ciInf_le ⟨0, by
    rintro _ ⟨S, rfl⟩
    exact one_div_nonneg.2 (muR_nonneg hr _ _)⟩ ⟨N, h0, rfl⟩

end CoefficientMass
