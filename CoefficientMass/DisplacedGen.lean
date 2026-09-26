/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.DisplacedTail
import CoefficientMass.TailSplitGen

/-!
# The Displaced Step at Arbitrary Nodes

This module proves the displaced step of Theorem 2.2 of `coefficient-mass-rows.tex`: for
nodes `0 < y_1 < ⋯ < y_c < 1`, deleting the largest prescribed zero together with the
largest node multiplies the tail by at most `max(1, φ_c)`, `φ_c = y_c / (1 - y_c)`.  The
argument is that of `tsum_le_lt_of_displaced` with the correction ratio
`(1 - y_c)^{-1}` in place of `2`.

## Theorems

* `tsum_le_of_displaced_gen`.
-/

namespace CoefficientMass

/-- The displaced step at nodes in `(0, 1)`: `Tail(w) ≤ max(1, φ_c) Tail(F)`. -/
theorem tsum_le_of_displaced_gen {n : ℕ} (y : Fin (n + 1) → ℝ) (hmono : StrictMono y)
    (hpos : ∀ i, 0 < y i) (hlt1 : ∀ i, y i < 1) (Z : Finset ℕ) {z : ℕ} (hz : z ∈ Z)
    (hzmax : ∀ τ ∈ Z, τ ≤ z) (h0 : 0 ∉ Z) (hcard : Z.card = n) (aw : Fin (n + 1) → ℝ)
    (hw : IsCertificate aw y Z) (aF : Fin n → ℝ)
    (hF : IsCertificate aF (fun i => y i.castSucc) (Z.erase z))
    (hFs : Summable fun d => |expSum aF (fun i => y i.castSucc) (d + 1)|) :
    ∑' d, |expSum aw y (d + 1)| ≤ max 1 (y (Fin.last n) / (1 - y (Fin.last n))) *
      ∑' d, |expSum aF (fun i => y i.castSucc) (d + 1)| := by
  have hy := hmono.injective
  set Z' := Z.erase z with hZ'def
  have hZ' : Z'.card + 1 = n := by
    rw [hZ'def, Finset.card_erase_of_mem hz, hcard]
    have := Finset.card_pos.2 ⟨z, hz⟩
    omega
  have h0' : 0 ∉ Z' := fun h => h0 (Finset.mem_of_mem_erase h)
  have hzpos : 0 < z := Nat.pos_of_ne_zero fun h => h0 (h ▸ hz)
  have hZ'z : ∀ τ ∈ Z', τ < z := fun τ hτ =>
    lt_of_le_of_ne (hzmax τ (Finset.mem_of_mem_erase hτ)) (Finset.ne_of_mem_erase hτ)
  have hAz : ∀ α ∈ insert 0 Z', α < z := fun α hα => by
    rcases Finset.mem_insert.1 hα with rfl | hα
    · exact hzpos
    · exact hZ'z α hα
  have hA : (insert 0 Z').card + 1 = n + 1 := by rw [Finset.card_insert_of_notMem h0', hZ']
  -- the sum `G`
  obtain ⟨aG, haG⟩ := exists_interp y hy hpos (insert 0 Z)
    (by rw [Finset.card_insert_of_notMem h0, hcard]) fun k => if k = z then 1 else 0
  have hGz : expSum aG y z = 1 := by rw [haG z (Finset.mem_insert_of_mem hz), if_pos rfl]
  have hG0 : ∀ k ∈ insert 0 Z', expSum aG y k = 0 := fun k hk => by
    have hkz : k ≠ z := fun h => lt_irrefl _ (h ▸ hAz k hk)
    rw [haG k (Finset.insert_subset_insert 0 (Finset.erase_subset z Z) hk), if_neg hkz]
  set m := (insert 0 Z').max' (Finset.insert_nonempty 0 Z') with hmdef
  have hm : m ∈ insert 0 Z' := Finset.max'_mem _ _
  have hmmax : ∀ τ ∈ Z', τ ≤ m := fun τ hτ => Finset.le_max' _ τ (Finset.mem_insert_of_mem hτ)
  have hmz : m < z := hAz m hm
  set η : ℝ := (-1) ^ Z'.card with hη
  set F := expSum aF (fun i => y i.castSucc) with hFdef
  set G := expSum aG y with hGdef
  set w := expSum aw y with hwdef
  have hF1 : F 0 = 1 := hF.1
  have hF2 : ∀ k ∈ Z', F k = 0 := hF.2
  have hw1 : w 0 = 1 := hw.1
  have hw2 : ∀ k ∈ Z, w k = 0 := hw.2
  have hy' : Function.Injective fun i : Fin n => y i.castSucc :=
    hy.comp (Fin.castSucc_injective n)
  have hpos' : ∀ i : Fin n, 0 < y i.castSucc := fun i => hpos _
  have hηη : η * η = 1 := neg_one_pow_mul_self _
  have hFb : ∀ d, 0 < d → (∀ τ ∈ Z', τ < d) → 0 < η * F d := fun d hd hdZ => by
    have := sign_of_certificate aF _ hy' hpos' _ hZ' h0' hF hd fun h => lt_irrefl _ (hdZ d h)
    rwa [Finset.filter_true_of_mem hdZ] at this
  have hμ : 0 < η * F z := hFb z hzpos hZ'z
  have habsF : ∀ d, 0 < η * F d → |F d| = η * F d := fun d h => by
    rw [← abs_of_pos h, abs_mul, hη, abs_neg_one_pow, one_mul]
  -- `w = F - F_z G`
  have hwFG : ∀ d, w d = F d - F z * G d := fun d => by
    have := expSum_eq_of_agree aw (fun i => Fin.snoc (α := fun _ => ℝ) aF 0 i - F z * aG i)
      y hy hpos (insert 0 Z) (by rw [Finset.card_insert_of_notMem h0, hcard]) (fun k hk => by
        rw [expSum_sub, expSum_mul_left, expSum_snoc]
        change w k = F k - F z * G k
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [hw1, hF1, hG0 0 (Finset.mem_insert_self 0 Z'), mul_zero, sub_zero]
        rcases eq_or_ne k z with rfl | hkz
        · rw [hw2 k hk, hGz, mul_one, sub_self]
        · have hk' : k ∈ Z' := Finset.mem_erase.2 ⟨hkz, hk⟩
          rw [hw2 k hk, hF2 k hk', hG0 k (Finset.mem_insert_of_mem hk'), mul_zero,
            sub_zero]) d
    change expSum aw y d = _
    rw [this, expSum_sub, expSum_mul_left, expSum_snoc]
  -- the sign patterns
  have hGpos : ∀ d, z ≤ d → 0 < G d := fun d hd =>
    pos_beyond aG y hy hpos _ hA hG0 hGz hAz fun α hα => (hAz α hα).trans_le hd
  have hlow : ∀ d, 1 ≤ d → d < z → |w d| ≤ |F d| ∧ (d ∉ Z' → |w d| < |F d|) :=
      fun d hd hdz => by
    by_cases hdZ' : d ∈ Z'
    · rw [hw2 d (Finset.mem_of_mem_erase hdZ'), abs_zero]
      exact ⟨abs_nonneg _, fun h => absurd hdZ' h⟩
    have hdZ : d ∉ Z := fun h => hdZ' (Finset.mem_erase.2 ⟨hdz.ne, h⟩)
    have hdA : d ∉ insert 0 Z' := by
      rw [Finset.mem_insert]
      exact fun h => h.elim (fun h => by omega) hdZ'
    have s1 := sign_of_certificate aF _ hy' hpos' _ hZ' h0' hF hd hdZ'
    have s2 := sign_before_top aG y hy hpos _ hA hG0 hGz hAz hdA hdz
    have s3 := sign_of_certificate aw y hy hpos Z (by rw [hcard]) h0 hw hd hdZ
    rw [Finset.filter_insert, if_neg (Nat.not_lt_zero d)] at s2
    have hZfilt : Z.filter (· < d) = Z'.filter (· < d) := by
      ext τ
      simp only [Finset.mem_filter, hZ'def, Finset.mem_erase]
      exact ⟨fun h => ⟨⟨fun h' => by omega, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    rw [hZfilt] at s3
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z') (· < d)
    have hnot : Z'.filter (fun τ => ¬τ < d) = Z'.filter (d < ·) :=
      Finset.filter_congr fun τ hτ => by
        constructor
        · intro h
          rcases lt_or_eq_of_le (not_lt.1 h) with h | h
          · exact h
          · exact absurd (h ▸ hτ) hdZ'
        · intro h
          exact not_lt.2 h.le
    rw [hnot] at hsplit
    set s : ℝ := (-1) ^ (Z'.filter (· < d)).card
    set t : ℝ := (-1) ^ (Z'.filter (d < ·)).card
    have hst : η = s * t := by rw [hη, ← hsplit, pow_add]
    have hss : s * s = 1 := neg_one_pow_mul_self _
    have htt : t * t = 1 := neg_one_pow_mul_self _
    have hFG : 0 < F d * G d * F z := by
      have := mul_pos (mul_pos s1 s2) hμ
      rw [hst] at this
      have h' : s * F d * (t * G d) * (s * t * F z) = (s * s) * (t * t) * (F d * G d * F z) := by
        ring
      rwa [h', hss, htt, one_mul, one_mul] at this
    have hWG : 0 ≤ w d * G d * F z := by
      have := mul_pos (mul_pos s3 s2) hμ
      rw [hst] at this
      have h' : s * w d * (t * G d) * (s * t * F z) = (s * s) * (t * t) * (w d * G d * F z) := by
        ring
      rw [h', hss, htt, one_mul, one_mul] at this
      exact this.le
    have hGd : G d ≠ 0 := fun h => by
      change 0 < t * G d at s2
      rw [h, mul_zero] at s2
      exact lt_irrefl 0 s2
    have hFz0 : F z ≠ 0 := fun h => by
      rw [h, mul_zero] at hμ
      exact lt_irrefl 0 hμ
    have hFG0 : 0 < |F z| * |G d| := mul_pos (abs_pos.2 hFz0) (abs_pos.2 hGd)
    rw [abs_eq_sub_of_pos (hwFG d) hFG hWG]
    exact ⟨by linarith, fun _ => by linarith⟩
  have hhigh : ∀ d, z < d → |w d| = η * F z * G d - |F d| := fun d hdz => by
    have hdZ' : ∀ τ ∈ Z', τ < d := fun τ hτ => (hZ'z τ hτ).trans hdz
    have hdZ : d ∉ Z := fun h => by have := hzmax d h; omega
    have s1 := hFb d (by omega) hdZ'
    have s2 := hGpos d hdz.le
    have s3 := sign_of_certificate aw y hy hpos Z (by rw [hcard]) h0 hw (by omega) hdZ
    rw [Finset.filter_true_of_mem fun τ hτ => (hzmax τ hτ).trans_lt hdz,
      ← Finset.card_erase_add_one hz, ← hZ'def, pow_succ, ← hη] at s3
    have hFG : 0 < F d * G d * F z := by
      have := mul_pos (mul_pos s1 s2) hμ
      have h' : η * F d * G d * (η * F z) = (η * η) * (F d * G d * F z) := by ring
      rwa [h', hηη, one_mul] at this
    have hWG : w d * G d * F z ≤ 0 := by
      have := mul_pos (mul_pos s3 s2) hμ
      have h' : η * -1 * w d * G d * (η * F z) = -((η * η) * (w d * G d * F z)) := by ring
      rw [h', hηη, one_mul] at this
      linarith
    rw [abs_eq_sub_of_neg (hwFG d) hFG hWG, abs_of_pos s2, ← habsF z hμ]
  -- the correction ratio
  have hyc0 := (hpos (Fin.last n)).le
  have hyc1 : 0 < 1 - y (Fin.last n) := by linarith [hlt1 (Fin.last n)]
  have hgamma : ∀ M, η * F z * ∑ t ∈ Finset.range (M + 1), G (z + t) ≤
      1 / (1 - y (Fin.last n)) * ∑ t ∈ Finset.range (M + 1), |F (z + t)| := fun M => by
    have h := gamma_bound_gen (fun t => G (z + t)) (fun t => |F (z + t)|) hyc0 hμ.le
      (fun t => (hGpos _ (Nat.le_add_right z t)).le)
      (by simp only [add_zero]; rw [hGz, mul_one, habsF z hμ]) (fun t => by
        have hd := drive y hy hpos Z hz hzmax h0 hcard aF hF aG hG0 hGz hm hmmax hmz hμ
          (e := z + t) (by omega)
        have hFe := hFb (z + t + 1) (by omega) fun τ hτ => by have := hZ'z τ hτ; omega
        change η * F z * G (z + (t + 1)) ≤
          η * F z * y (Fin.last n) * G (z + t) + |F (z + (t + 1))|
        rw [show z + (t + 1) = z + t + 1 by ring, habsF _ hFe]
        linarith) M
    rw [one_div_mul_eq_div, le_div_iff₀ hyc1]
    linarith
  have hle : ∀ d, 1 ≤ d → d < z → |w d| ≤ |F d| := fun d h1 h2 => (hlow d h1 h2).1
  have hκ : (1 : ℝ) ≤ 1 / (1 - y (Fin.last n)) :=
    one_le_one_div hyc1 (by linarith)
  have hκ' : 1 / (1 - y (Fin.last n)) - 1 = y (Fin.last n) / (1 - y (Fin.last n)) := by
    rw [div_sub_one hyc1.ne']
    ring
  have := tsum_abs_le_of_split_gen w F G hzpos hκ hle (hw2 z hz) (habsF z hμ) hGz hhigh hgamma
    hFs
  rwa [hκ'] at this

end CoefficientMass
