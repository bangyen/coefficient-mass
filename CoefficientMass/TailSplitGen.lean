/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.TailSplit

/-!
# The Tail Split at Arbitrary Nodes

This module prepares Theorem 2.2 of `coefficient-mass-rows.tex`, the tail bound at nodes in
`(0, 1)`.  Without `y_c ≤ 1/2` the correction ratio is `μ ∑ G ≤ (1 - y_c)^{-1} ∑ |F|`, and
the tail split then gives `Tail(w) ≤ max(1, κ - 1) Tail(F)` with `κ = (1 - y_c)^{-1}`, so
`κ - 1 = y_c / (1 - y_c)`.

## Theorems

* `gamma_bound_gen`.
* `tsum_abs_le_of_split_gen`.
-/

namespace CoefficientMass

/-- The correction ratio at any `y_c < 1`: `(1 - y_c) μ ∑_{t ≤ M} g_t ≤ ∑_{t ≤ M} f_t`. -/
theorem gamma_bound_gen (g f : ℕ → ℝ) {yc μ : ℝ} (hyc0 : 0 ≤ yc) (hμ : 0 ≤ μ)
    (hg : ∀ t, 0 ≤ g t) (h0 : μ * g 0 = f 0)
    (hrec : ∀ t, μ * g (t + 1) ≤ μ * yc * g t + f (t + 1)) (M : ℕ) :
    (1 - yc) * (μ * ∑ t ∈ Finset.range (M + 1), g t) ≤ ∑ t ∈ Finset.range (M + 1), f t := by
  have hA := Finset.sum_range_succ' g M
  have hB := Finset.sum_range_succ g M
  have hC := Finset.sum_range_succ' f M
  have h1 : ∑ t ∈ Finset.range M, μ * g (t + 1) ≤
      ∑ t ∈ Finset.range M, (μ * yc * g t + f (t + 1)) := Finset.sum_le_sum fun t _ => hrec t
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have hX1 : μ * ∑ t ∈ Finset.range (M + 1), g t ≤
      μ * yc * ∑ t ∈ Finset.range M, g t + ∑ t ∈ Finset.range (M + 1), f t := by
    rw [hA, hC, mul_add]
    linarith
  have hX2 : μ * yc * ∑ t ∈ Finset.range M, g t ≤
      yc * (μ * ∑ t ∈ Finset.range (M + 1), g t) := by
    rw [hB]
    nlinarith [mul_nonneg (mul_nonneg hμ hyc0) (hg M)]
  linarith

/-- The tail split with the correction ratio `κ ≥ 1`: `Tail(w) ≤ max(1, κ - 1) Tail(F)`. -/
theorem tsum_abs_le_of_split_gen (w F G : ℕ → ℝ) {z : ℕ} (hz : 1 ≤ z) {μ κ : ℝ}
    (hκ : 1 ≤ κ) (hlow : ∀ d, 1 ≤ d → d < z → |w d| ≤ |F d|) (hwz : w z = 0)
    (hFz : |F z| = μ) (hGz : G z = 1) (hhigh : ∀ d, z < d → |w d| = μ * G d - |F d|)
    (hgamma : ∀ M, μ * ∑ t ∈ Finset.range (M + 1), G (z + t) ≤
      κ * ∑ t ∈ Finset.range (M + 1), |F (z + t)|)
    (hsum : Summable fun d => |F (d + 1)|) :
    ∑' d, |w (d + 1)| ≤ max 1 (κ - 1) * ∑' d, |F (d + 1)| := by
  obtain ⟨z0, rfl⟩ : ∃ z0, z = z0 + 1 := ⟨z - 1, by omega⟩
  have hm1 : (1 : ℝ) ≤ max 1 (κ - 1) := le_max_left _ _
  have hmκ : κ - 1 ≤ max 1 (κ - 1) := le_max_right _ _
  have hmain : ∀ N, ∑ d ∈ Finset.range (z0 + (N + 1)), |w (d + 1)| ≤
      max 1 (κ - 1) * ∑ d ∈ Finset.range (z0 + (N + 1)), |F (d + 1)| := by
    intro N
    rw [Finset.sum_range_add (fun d => |w (d + 1)|) z0 (N + 1),
      Finset.sum_range_add (fun d => |F (d + 1)|) z0 (N + 1),
      Finset.sum_range_succ' (fun k => |w (z0 + k + 1)|) N,
      Finset.sum_range_succ' (fun k => |F (z0 + k + 1)|) N, add_zero, hwz, abs_zero, add_zero,
      hFz]
    have hlowsum : ∑ d ∈ Finset.range z0, |w (d + 1)| ≤ ∑ d ∈ Finset.range z0, |F (d + 1)| :=
      Finset.sum_le_sum fun d hd => hlow _ (by omega) (by have := Finset.mem_range.1 hd; omega)
    have hhighsum : ∑ k ∈ Finset.range N, |w (z0 + (k + 1) + 1)| =
        ∑ k ∈ Finset.range N, (μ * G (z0 + 1 + (k + 1)) - |F (z0 + 1 + (k + 1))|) :=
      Finset.sum_congr rfl fun k _ => by
        rw [hhigh _ (by omega), show z0 + (k + 1) + 1 = z0 + 1 + (k + 1) by ring]
    have hFsum : ∑ k ∈ Finset.range N, |F (z0 + (k + 1) + 1)| =
        ∑ k ∈ Finset.range N, |F (z0 + 1 + (k + 1))| :=
      Finset.sum_congr rfl fun k _ => by rw [show z0 + (k + 1) + 1 = z0 + 1 + (k + 1) by ring]
    have hg := hgamma N
    rw [Finset.sum_range_succ' (fun t => G (z0 + 1 + t)) N,
      Finset.sum_range_succ' (fun t => |F (z0 + 1 + t)|) N, hGz, hFz] at hg
    rw [hhighsum, hFsum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hlow0 : 0 ≤ ∑ d ∈ Finset.range z0, |F (d + 1)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hhigh0 : 0 ≤ ∑ k ∈ Finset.range N, |F (z0 + 1 + (k + 1))| + μ := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range N) => abs_nonneg (F (z0 + 1 + (k + 1)))
      have hμ : 0 ≤ μ := hFz ▸ abs_nonneg _
      linarith
    have k1 := mul_le_mul_of_nonneg_right hm1 hlow0
    have k2 := mul_le_mul_of_nonneg_right hmκ hhigh0
    nlinarith
  refine Real.tsum_le_of_sum_range_le (fun d => abs_nonneg _) fun N => ?_
  calc ∑ d ∈ Finset.range N, |w (d + 1)|
      ≤ ∑ d ∈ Finset.range (z0 + (N + 1)), |w (d + 1)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun _ _ _ => abs_nonneg _
    _ ≤ max 1 (κ - 1) * ∑ d ∈ Finset.range (z0 + (N + 1)), |F (d + 1)| := hmain N
    _ ≤ max 1 (κ - 1) * ∑' d, |F (d + 1)| :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun _ _ => abs_nonneg _) (by linarith)

end CoefficientMass
