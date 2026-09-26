/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.ValsBlock

/-!
# Moving a Kept Hole Down

This module proves the middle step of Lemma 4.10 of `coefficient-mass.tex`.  For the
`r`-th kept hole (from `0`) at `c`, the bound on `2^{-c} |ψ(c)|` is
`W_r(c) = 2^{-c} c B(ℓ - r + q + 1, c) · (ℓ + 1) / (c - ℓ - 1) · C(c - 1, r - 1) ·
C(c + ℓ - r, ℓ - r)`.  For `c ≥ ℓ + 1 + r`, `W_r(c + 1) / W_r(c) ≤ c / (2(c - r + 1)) ≤ 1`,
so `W_r(c) ≤ W_r(ℓ + 1 + r)`, the value for the block `{ℓ + 1, …, 2ℓ + 1}`.

## Definitions

* `pDown`.
* `qUp`.
* `holeW`.

## Theorems

* `pDown_succ`.
* `qUp_succ`.
* `betaI_shift`.
* `ratio_le`.
* `betaI_nonneg`.
* `pDown_nonneg`.
* `holeW_succ_le`.
* `holeW_le`.
-/

namespace CoefficientMass

/-- `∏_{j < k} (c - 1 - j) / (j + 1) = C(c - 1, k)`. -/
noncomputable def pDown (k c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (((c : ℝ) - 1 - j) / (j + 1))

/-- `∏_{j < k} (c + 1 + j) / (j + 1) = C(c + k, k)`. -/
noncomputable def qUp (k c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (((c : ℝ) + 1 + j) / (j + 1))

/-- `W_r(c)` for `r ≥ 1`. -/
noncomputable def holeW (ℓ q r c : ℕ) : ℝ :=
  (1 / 2) ^ c * ((c : ℝ) * betaI (ℓ - r + q) (c - 1)) *
    (((ℓ : ℝ) + 1) / ((c : ℝ) - ℓ - 1) * pDown (r - 1) c) * qUp (ℓ - r) c

theorem pDown_succ (k c : ℕ) : pDown k (c + 1) * ((c : ℝ) - k) = pDown k c * c := by
  induction k with
  | zero =>
    rw [pDown, pDown, Finset.prod_range_zero, Finset.prod_range_zero]
    push_cast
    ring
  | succ k ih =>
    rw [pDown, pDown, Finset.prod_range_succ, Finset.prod_range_succ, ← pDown, ← pDown]
    have h : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show pDown k (c + 1) * (((c : ℝ) + 1 - 1 - k) / (k + 1)) * (c - (k + 1)) =
      pDown k (c + 1) * (c - k) * ((c - 1 - k) / (k + 1)) by ring, ih]
    ring

theorem qUp_succ (k c : ℕ) : qUp k (c + 1) * ((c : ℝ) + 1) = qUp k c * ((c : ℝ) + 1 + k) := by
  induction k with
  | zero =>
    rw [qUp, qUp, Finset.prod_range_zero, Finset.prod_range_zero]
    ring
  | succ k ih =>
    rw [qUp, qUp, Finset.prod_range_succ, Finset.prod_range_succ, ← qUp, ← qUp]
    push_cast
    rw [show qUp k (c + 1) * (((c : ℝ) + 1 + 1 + k) / (k + 1)) * (c + 1) =
      qUp k (c + 1) * (c + 1) * ((c + 1 + 1 + k) / (k + 1)) by ring, ih]
    ring

/-- `(c + 1) B(a + 1, c + 1) (a + c + 1) = c B(a + 1, c) (c + 1)` for `c ≥ 1`. -/
theorem betaI_shift (a c : ℕ) (hc : 1 ≤ c) :
    ((c : ℝ) + 1) * betaI a c * ((a : ℝ) + c + 1) = (c : ℝ) * betaI a (c - 1) * (c + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [betaI_eq, betaI_eq, Nat.add_sub_cancel, show a + (d + 1) + 1 = a + d + 1 + 1 by ring,
    Nat.factorial_succ (a + d + 1), Nat.factorial_succ d]
  have h1 : ((a + d + 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem ratio_le {c ℓ r a : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ ℓ) (h3 : ℓ + 1 + r ≤ c)
    (h4 : ℓ - r ≤ a) : 1 / 2 * c * (c + 1 + (ℓ - r)) * (c - ℓ - 1) ≤
      (c - (r - 1)) * (a + c + 1) * (c - ℓ) := by
  have e1 : 1 / 2 * c ≤ c - (r - 1) := by linarith
  have e2 : c + 1 + (ℓ - r) ≤ a + c + 1 := by linarith
  have e3 : c - ℓ - 1 ≤ c - ℓ := by linarith
  have p1 : 0 ≤ 1 / 2 * c := by linarith
  have p2 : 0 ≤ c + 1 + (ℓ - r) := by linarith
  have p3 : 0 ≤ c - ℓ - 1 := by linarith
  calc 1 / 2 * c * (c + 1 + (ℓ - r)) * (c - ℓ - 1)
      ≤ (c - (r - 1)) * (a + c + 1) * (c - ℓ - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 p2 (by linarith)) p3
    _ ≤ (c - (r - 1)) * (a + c + 1) * (c - ℓ) :=
        mul_le_mul_of_nonneg_left e3 (mul_nonneg (by linarith) (by linarith))

theorem betaI_nonneg (a b : ℕ) : 0 ≤ betaI a b := by
  rw [betaI_eq]
  positivity

theorem pDown_nonneg {k c : ℕ} (hk : k + 1 ≤ c) : 0 ≤ pDown k c :=
  Finset.prod_nonneg fun j hj => by
    have hj := Finset.mem_range.1 hj
    have : (j : ℝ) + 1 ≤ c := by exact_mod_cast (show j + 1 ≤ c by omega)
    exact div_nonneg (by linarith) (by positivity)

/-- `W_r(c + 1) ≤ W_r(c)` for `1 ≤ r ≤ ℓ` and `c ≥ ℓ + 1 + r`. -/
theorem holeW_succ_le {ℓ q r c : ℕ} (hr1 : 1 ≤ r) (hrl : r ≤ ℓ) (hc : ℓ + 1 + r ≤ c) :
    holeW ℓ q r (c + 1) ≤ holeW ℓ q r c := by
  have eT := betaI_shift (ℓ - r + q) c (by omega)
  have eP := pDown_succ (r - 1) c
  have eQ := qUp_succ (ℓ - r) c
  have hcr : ((c : ℝ) - ((r - 1 : ℕ) : ℝ)) = (c : ℝ) - (r - 1) := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  have hlr : (((ℓ - r : ℕ) : ℝ)) = (ℓ : ℝ) - r := Nat.cast_sub hrl
  have ha : (((ℓ - r + q : ℕ) : ℝ)) = (ℓ : ℝ) - r + q := by rw [Nat.cast_add, hlr]
  have hcR : (ℓ : ℝ) + 1 + r ≤ c := by exact_mod_cast hc
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrlR : (r : ℝ) ≤ ℓ := by exact_mod_cast hrl
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [hcr] at eP
  rw [hlr] at eQ
  rw [ha] at eT
  have d1 : (ℓ : ℝ) - r + q + c + 1 ≠ 0 := by linarith
  have d2 : (c : ℝ) - (r - 1) ≠ 0 := by linarith
  have d3 : (c : ℝ) + 1 ≠ 0 := by linarith
  have d4 : (c : ℝ) + 1 - ℓ - 1 ≠ 0 := by linarith
  have d5 : (c : ℝ) - ℓ - 1 ≠ 0 := by linarith
  have d6 : (c : ℝ) - ℓ ≠ 0 := by linarith
  set t := (c : ℝ) * betaI (ℓ - r + q) (c - 1) with ht
  set P := pDown (r - 1) c
  set Q := qUp (ℓ - r) c
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg c) (betaI_nonneg _ _)
  have hP0 : 0 ≤ P := pDown_nonneg (by omega)
  have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun j _ => by positivity
  have e1 : ((c : ℝ) + 1) * betaI (ℓ - r + q) c = t * (c + 1) / ((ℓ : ℝ) - r + q + c + 1) := by
    rw [eq_div_iff d1, ← eT]
  have e2 : pDown (r - 1) (c + 1) = P * c / ((c : ℝ) - (r - 1)) := by rw [eq_div_iff d2, eP]
  have e3 : qUp (ℓ - r) (c + 1) = Q * (c + 1 + ((ℓ : ℝ) - r)) / ((c : ℝ) + 1) := by
    rw [eq_div_iff d3, eQ]
  have key := ratio_le hr1R hrlR hcR (show (ℓ : ℝ) - r ≤ ℓ - r + q by linarith)
  rw [holeW, holeW, Nat.add_sub_cancel]
  push_cast
  rw [e1, e2, e3]
  have hX : 0 ≤ (1 / 2 : ℝ) ^ c * t * ((ℓ + 1) * P) * Q := by positivity
  calc (1 / 2 : ℝ) ^ (c + 1) * (t * (c + 1) / ((ℓ : ℝ) - r + q + c + 1)) *
        ((ℓ + 1) / ((c : ℝ) + 1 - ℓ - 1) * (P * c / ((c : ℝ) - (r - 1)))) *
        (Q * (c + 1 + ((ℓ : ℝ) - r)) / ((c : ℝ) + 1))
      = (1 / 2 : ℝ) ^ c * t * ((ℓ + 1) * P) * Q * (1 / 2 * c * (c + 1 + ((ℓ : ℝ) - r)) /
          (((c : ℝ) - (r - 1)) * ((ℓ : ℝ) - r + q + c + 1) * ((c : ℝ) - ℓ))) := by
        field_simp
        ring
    _ ≤ (1 / 2 : ℝ) ^ c * t * ((ℓ + 1) * P) * Q * (1 / ((c : ℝ) - ℓ - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hX
        have p1 : (0 : ℝ) < (c : ℝ) - (r - 1) := by linarith
        have p2 : (0 : ℝ) < (ℓ : ℝ) - r + q + c + 1 := by linarith
        have p3 : (0 : ℝ) < (c : ℝ) - ℓ := by linarith
        rw [div_le_div_iff₀ (mul_pos (mul_pos p1 p2) p3) (by linarith)]
        linarith
    _ = (1 / 2 : ℝ) ^ c * t * ((ℓ + 1) / ((c : ℝ) - ℓ - 1) * P) * Q := by
        ring

/-- `W_r(c) ≤ W_r(ℓ + 1 + r)` for `c ≥ ℓ + 1 + r`. -/
theorem holeW_le {ℓ q r : ℕ} (hr1 : 1 ≤ r) (hrl : r ≤ ℓ) :
    ∀ d, holeW ℓ q r (ℓ + 1 + r + d) ≤ holeW ℓ q r (ℓ + 1 + r) := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [← add_assoc]
    exact (holeW_succ_le hr1 hrl (by omega)).trans ih

end CoefficientMass
