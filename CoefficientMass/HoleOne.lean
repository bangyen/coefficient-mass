/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleInt

/-!
# One Hole

This module evaluates the one-hole case of Lemma 4.7 of `coefficient-mass.tex`:
for `C = {1}` and `C = {2}` the weight of Lemma 4.7 is `M_C ≡ 1`, so
`Φ({2, …, N}) = 1 / N` and `Φ({1, …, N} \ {2}) = 1 / (N - 1)`.

## Theorems

* `confTail_hole_one`.
* `confTail_hole_two`.
-/

open intervalIntegral

namespace CoefficientMass

/-- `Φ({2, …, N}) = 1 / N`. -/
theorem confTail_hole_one {N : ℕ} (hN : 1 ≤ N) : confTail (Finset.Icc 1 N \ {1}) = 1 / N := by
  have hw : holeWeight {1} 1 = 1 := by
    rw [holeWeight, Finset.prod_singleton, Finset.erase_singleton, Finset.prod_empty,
      Nat.cast_one, div_one]
  rw [holeIntegral N {1} (Finset.singleton_nonempty 1)
    (fun h => absurd (Finset.mem_singleton.1 h) (by norm_num))
    (fun c hc => by rw [Finset.mem_singleton.1 hc]; exact hN)]
  simp only [Finset.sum_singleton, hw]
  rw [integral_congr (g := fun v : ℝ => v ^ (N - 1)) fun v _ => by
      simp only [abs_one, Nat.sub_self, pow_zero, mul_one]; ring, integral_pow]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.cast_add,
    Nat.cast_one]

/-- `Φ({1, …, N} \ {2}) = 1 / (N - 1)`. -/
theorem confTail_hole_two {N : ℕ} (hN : 2 ≤ N) :
    confTail (Finset.Icc 1 N \ {2}) = 1 / ((N : ℝ) - 1) := by
  have hw : holeWeight {2} 2 = 2 := by
    rw [holeWeight, Finset.prod_singleton, Finset.erase_singleton, Finset.prod_empty, div_one,
      Nat.cast_ofNat]
  rw [holeIntegral N {2} (Finset.singleton_nonempty 2)
    (fun h => absurd (Finset.mem_singleton.1 h) (by norm_num))
    (fun c hc => by rw [Finset.mem_singleton.1 hc]; exact hN)]
  simp only [Finset.sum_singleton, hw]
  rw [integral_congr (g := fun v : ℝ => v ^ (N - 2)) fun v _ => by
      simp only [abs_two, pow_one]; ring, integral_pow]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Nat.add_sub_cancel, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero,
    show ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 by push_cast; ring]

end CoefficientMass
