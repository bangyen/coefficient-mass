/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Consecutive

/-!
# The Displaced-Zero Tail Bound

This module begins Theorem 2.2 of `coefficient-mass.tex`.  The paper inducts
on the number of displaced zeros; the base case, no displaced zeros, is
Lemma 2.1 with the factors beyond the leading run dropped, each being at most
one because the nodes are at most `1/2`.  The displaced step rests on
Lemma 2.3, a zero count with multiplicity for a correction sum, and is not
yet formalized.

## Theorems

* `tailBound_consecutive`.
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

end CoefficientMass
