/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.HoleFree
import CoefficientMass.TailBound
import CoefficientMass.ValsMain

/-!
# Every Row at the Root Two

This module proves Proposition 4.12 and Theorem 4.13 of `coefficient-mass.tex`.  For
`{1, 2, 3} ⊆ A` with leading run `ℓ ≥ 3`, keep the first `ℓ + 1` holes, fill the next
`n - 1`, and put `N = c_{ℓ+n}`, `m = c_{ℓ+1}`, `q = N - m ≥ n - 1`.  Splitting `Φ(Y)` at
`N`, Lemmas 4.10 and 4.11 give
`Φ(Y) ≤ (1/2 + (ℓ + 1) / (e ℓ)) / (q + 1) ≤ 1 / (q + 1) ≤ 1 / n`.  Together with
Proposition 4.9 this is `(∗_n)` for every `n ≥ 1`, and Lemma 4.5 gives every row.

## Definitions

* `RowsTop`.

## Theorems

* `confTail_split`.
* `tail_le_half`.
* `rowsTop`.
* `star`.
* `everyRow`.
-/

namespace CoefficientMass

/-- Proposition 4.12 (rows at the top three positions): for `n ≥ 1` and finite
`A ⊂ ℕ_{>0}` with `{1, 2, 3} ⊆ A`, some finite `Z ⊇ A` has `|Z| ≤ |A| + n - 1` and
`Φ(Z) ≤ 1 / n`. -/
def RowsTop : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A : Finset ℕ, 0 ∉ A → {1, 2, 3} ⊆ A →
    ∃ Z : Finset ℕ, A ⊆ Z ∧ 0 ∉ Z ∧ Z.card + 1 ≤ A.card + n ∧ confTail Z ≤ 1 / n

/-- `Φ({1, …, N} \ C)` is the sum over the holes plus the tail beyond `N`. -/
theorem confTail_split {N : ℕ} {C : Finset ℕ} (h0 : 0 ∉ C) (hle : ∀ c ∈ C, c ≤ N) :
    confTail (Finset.Icc 1 N \ C) =
      ∑ c ∈ C, |confPoly (Finset.Icc 1 N \ C) c| * (1 / 2 : ℝ) ^ c +
        ∑' t : ℕ, |confPoly (Finset.Icc 1 N \ C) (t + N + 1)| * (1 / 2 : ℝ) ^ (t + N + 1) := by
  have hsub : C ⊆ Finset.Icc 1 N := fun p hp =>
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hp), hle p hp⟩
  set Y := Finset.Icc 1 N \ C
  have hfin : ∑ d ∈ Finset.range N, |confPoly Y (d + 1)| * (1 / 2 : ℝ) ^ (d + 1) =
      ∑ c ∈ C, |confPoly Y c| * (1 / 2 : ℝ) ^ c := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun s => |confPoly Y s| * (1 / 2 : ℝ) ^ s),
      zero_add, Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_sdiff hsub,
      Finset.sum_eq_zero fun p hp => ?_, zero_add]
    have hp0 : p ≠ 0 := by have := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hp).1).1; omega
    rw [confPoly, Finset.prod_eq_zero hp (by rw [div_self (by exact_mod_cast hp0), sub_self]),
      abs_zero, zero_mul]
  rw [confTail, ← (summable_confTail Y).sum_add_tsum_nat_add N, hfin]

/-- `(ℓ + 1) / (e ℓ (q + 1)) ≤ 1 / (2(q + 1))` for `ℓ ≥ 3`, as `8 < 3e`. -/
theorem tail_le_half {ℓ q : ℕ} (hℓ : 3 ≤ ℓ) :
    ((ℓ : ℝ) + 1) / (Real.exp 1 * ℓ * (q + 1)) ≤ 1 / (2 * ((q : ℝ) + 1)) := by
  have hℓR : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have he := mul_le_mul_of_nonneg_right Real.exp_one_gt_d9.le (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
  have k1 : 2 * ((ℓ : ℝ) + 1) ≤ Real.exp 1 * ℓ := by linarith
  have hQ : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have k2 := mul_le_mul_of_nonneg_right k1 hQ.le
  rw [div_le_div_iff₀ (mul_pos (mul_pos (Real.exp_pos 1) (by linarith)) hQ) (by positivity)]
  nlinarith

/-- Proposition 4.12 (rows at the top three positions). -/
theorem rowsTop : RowsTop := by
  intro n hn A h0 hA
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    exact star_one h0
  have hc : 4 ≤ hole A 0 := by
    have hm := (hole_mem A 0).2
    have hpos := (hole_mem A 0).1
    by_contra h
    have : hole A 0 ∈ ({1, 2, 3} : Finset ℕ) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      omega
    exact hm (hA this)
  set ℓ := hole A 0 - 1 with hℓ
  have hmono := (hole_strictMono A).monotone
  have hinj := (hole_strictMono A).injective
  set C := (Finset.range (ℓ + 1)).image (hole A) with hCdef
  obtain ⟨hsub, hZ0, hcard, hΦ⟩ := fill_holes h0 (r := ℓ + 1) (by omega) hn (K := C) rfl rfl
  refine ⟨_, hsub, hZ0, hcard, hΦ.trans ?_⟩
  set m := hole A ℓ
  have hN := hole_add_le A ℓ (n - 1)
  rw [show ℓ + (n - 1) = ℓ + 1 + n - 2 by omega] at hN
  set q := hole A (ℓ + 1 + n - 2) - m with hqd
  rw [show hole A (ℓ + 1 + n - 2) = m + q by omega]
  have hCc : C.card = ℓ + 1 := by rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hl : ℓ + 1 ∈ C :=
    Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), by omega⟩
  have hm : m ∈ C := Finset.mem_image.2 ⟨ℓ, Finset.mem_range.2 (by omega), rfl⟩
  have hCm : ∀ c ∈ C, ℓ + 1 ≤ c ∧ c ≤ m := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
    have h1 := hmono (Nat.zero_le i)
    have h2 := hmono (show i ≤ ℓ by have := Finset.mem_range.1 hi; omega)
    omega
  have hC0 : 0 ∉ C := fun h => by have := (hCm 0 h).1; omega
  have hq : 1 ≤ q := by omega
  rw [confTail_split hC0 fun c hc => by have := (hCm c hc).2; omega]
  have hV := holeVals ℓ q m C hq hCc hl hCm
  have hT := holeTail ℓ q m C (by omega) hq hCc hl hm hCm
  have hT' := hT.trans (tail_le_half (q := q) (show 3 ≤ ℓ by omega))
  have hQ : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hnq : (n : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast (show n ≤ q + 1 by omega)
  calc _ ≤ 1 / (2 * ((q : ℝ) + 1)) + 1 / (2 * ((q : ℝ) + 1)) := add_le_add hV hT'
    _ = 1 / ((q : ℝ) + 1) := by
        rw [div_add_div_same, div_eq_div_iff (by positivity) (by positivity)]
        ring
    _ ≤ 1 / n := one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega)) hnq

/-- `(∗_n)` for every `n ≥ 1`. -/
theorem star (n : ℕ) (hn : 1 ≤ n) : Star n := by
  intro A h0
  by_cases hA : {1, 2, 3} ⊆ A
  · exact rowsTop n hn A h0 hA
  · exact rowsFree n hn A h0 hA

/-- Theorem 4.13 (every row at the root `2`). -/
theorem everyRow : EveryRow :=
  everyRow_of_star star

end CoefficientMass
