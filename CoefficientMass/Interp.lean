/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Signs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Interpolation and the Correction Sum

Tools for the displaced step of Theorem 2.2 in `coefficient-mass.tex`: sums
on `c` nodes can take any values at `c` naturals; a sum on the smaller nodes
is a sum on all of them with a zero coefficient; and `E_d = G_d - y_c G_{d-1}`
is a sum on the smaller nodes.

## Theorems

* `exists_interp`.
* `expSum_snoc`.
* `expSum_correction`.
* `neg_one_pow_mul_self`.
* `abs_eq_sub_of_pos`.
* `abs_eq_sub_of_neg`.
-/

namespace CoefficientMass

/-- The generalized Vandermonde system is solvable for any values. -/
theorem exists_interp {c : ℕ} (y : Fin c → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i) (S : Finset ℕ) (hS : S.card = c) (v : ℕ → ℝ) :
    ∃ a, ∀ k ∈ S, expSum a y k = v k := by
  let M : (Fin c → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun a k => expSum a y k
      map_add' := fun a b => by
        funext k
        simp only [expSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun t a => by
        funext k
        simp only [expSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have := card_add_one_le_of_zeros a y hy hpos hne S fun k hk => congrFun ha ⟨k, hk⟩
    omega
  have hrank : Module.finrank ℝ (Fin c → ℝ) = Module.finrank ℝ (S → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hS]
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
    fun k => v k.val
  exact ⟨a, fun k hk => congrFun ha ⟨k, hk⟩⟩

/-- A sum on the smaller nodes is a sum on all nodes with last coefficient zero. -/
theorem expSum_snoc {n : ℕ} (a : Fin n → ℝ) (y : Fin (n + 1) → ℝ) (d : ℕ) :
    expSum (Fin.snoc (α := fun _ => ℝ) a 0) y d = expSum a (fun i => y i.castSucc) d := by
  rw [expSum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
  rfl

/-- `E_{e+1} = G_{e+1} - y_c G_e` is a sum on the smaller nodes. -/
theorem expSum_correction {n : ℕ} (a y : Fin (n + 1) → ℝ) (hpos : ∀ i, 0 < y i) (e : ℕ) :
    expSum (fun i => a i.castSucc * (1 - y (Fin.last n) / y i.castSucc))
        (fun i => y i.castSucc) (e + 1) =
      expSum a y (e + 1) - y (Fin.last n) * expSum a y e := by
  simp only [expSum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
  have hl : a (Fin.last n) * y (Fin.last n) ^ (e + 1) -
      y (Fin.last n) * (a (Fin.last n) * y (Fin.last n) ^ e) = 0 := by ring
  rw [hl, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hpos i.castSucc).ne'
  field_simp
  ring

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- If `F, G` and `F_z` have product signs `F G F_z > 0` and `W = F - F_z G`
has `W G F_z ≥ 0`, then `|W| = |F| - |F_z| |G|`. -/
theorem abs_eq_sub_of_pos {W F G Fz : ℝ} (hW : W = F - Fz * G) (hFG : 0 < F * G * Fz)
    (hWG : 0 ≤ W * G * Fz) : |W| = |F| - |Fz| * |G| := by
  have hG : 0 < |G| * |Fz| := by
    rw [← abs_mul]
    exact abs_pos.2 fun h => by
      have : F * G * Fz = F * (G * Fz) := by ring
      rw [this, h, mul_zero] at hFG
      exact lt_irrefl _ hFG
  have h1 : |F| * |G| * |Fz| = F * G * Fz := by rw [← abs_mul, ← abs_mul, abs_of_pos hFG]
  have h2 : |W| * |G| * |Fz| = W * G * Fz := by rw [← abs_mul, ← abs_mul, abs_of_nonneg hWG]
  have h3 : W * G * Fz = F * G * Fz - (|Fz| * |G|) ^ 2 := by
    rw [hW, mul_pow, sq_abs, sq_abs]
    ring
  have : (|W| - (|F| - |Fz| * |G|)) * (|G| * |Fz|) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- The mirror of `abs_eq_sub_of_pos` when `W G F_z ≤ 0`. -/
theorem abs_eq_sub_of_neg {W F G Fz : ℝ} (hW : W = F - Fz * G) (hFG : 0 < F * G * Fz)
    (hWG : W * G * Fz ≤ 0) : |W| = |Fz| * |G| - |F| := by
  have hG : 0 < |G| * |Fz| := by
    rw [← abs_mul]
    exact abs_pos.2 fun h => by
      have : F * G * Fz = F * (G * Fz) := by ring
      rw [this, h, mul_zero] at hFG
      exact lt_irrefl _ hFG
  have h1 : |F| * |G| * |Fz| = F * G * Fz := by rw [← abs_mul, ← abs_mul, abs_of_pos hFG]
  have h2 : |W| * |G| * |Fz| = -(W * G * Fz) := by
    rw [← abs_mul, ← abs_mul, abs_of_nonpos hWG]
  have h3 : W * G * Fz = F * G * Fz - (|Fz| * |G|) ^ 2 := by
    rw [hW, mul_pow, sq_abs, sq_abs]
    ring
  have : (|W| - (|Fz| * |G| - |F|)) * (|G| * |Fz|) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

end CoefficientMass
