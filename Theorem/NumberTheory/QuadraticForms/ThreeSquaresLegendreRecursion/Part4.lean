/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part4


namespace MetaMathlibExt

lemma r3leg_smul_quatDiv (q : Quaternion ℤ) (c : ℤ)
    (hre : c ∣ q.re) (hI : c ∣ q.imI) (hJ : c ∣ q.imJ) (hK : c ∣ q.imK) :
    c • r3legQuatDiv q c = q := by
  apply Quaternion.ext
  · change c * (q.re / c) = q.re
    exact Int.mul_ediv_cancel' hre
  · change c * (q.imI / c) = q.imI
    exact Int.mul_ediv_cancel' hI
  · change c * (q.imJ / c) = q.imJ
    exact Int.mul_ediv_cancel' hJ
  · change c * (q.imK / c) = q.imK
    exact Int.mul_ediv_cancel' hK

lemma r3leg_descend_even {p m : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (q : Quaternion ℤ) (w : r3legModVec p)
    (hm : 0 < m) (hm2 : 2 ∣ m)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ q' : Quaternion ℤ,
      Quaternion.normSq q' = ((m / 2 : ℕ) : ℤ) * p ∧
      0 < m / 2 ∧ m / 2 < m ∧ r3legAligned p q' w := by
  have hnorm2 : (2 : ℤ) ∣ Quaternion.normSq q := by
    obtain ⟨k, hk⟩ := hm2
    refine ⟨(k : ℤ) * p, ?_⟩
    rw [hnorm, hk]
    push_cast
    ring
  obtain ⟨e, he, hre, hI, hJ, hK⟩ := r3leg_even_right_factor q hnorm2
  let q' := r3legQuatDiv (q * e) 2
  have hscale : (2 : ℤ) • q' = q * e := by
    exact r3leg_smul_quatDiv _ _ hre hI hJ hK
  have hnscale := congrArg Quaternion.normSq hscale
  rw [Quaternion.normSq_smul, map_mul, he, hnorm] at hnscale
  have hnorm' : Quaternion.normSq q' = ((m / 2 : ℕ) : ℤ) * p := by
    obtain ⟨k, hk⟩ := hm2
    subst m
    norm_num at hnscale ⊢
    nlinarith
  have hmdivpos : 0 < m / 2 := Nat.div_pos (by omega) (by decide)
  have hmdivlt : m / 2 < m := Nat.div_lt_self hm (by decide)
  have htwo : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hnat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hnat
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  refine ⟨q', hnorm', hmdivpos, hmdivlt, ?_⟩
  exact r3leg_aligned_transfer htwo hscale halign

lemma r3leg_bmod_sq_le (z : ℤ) (k : ℕ) :
    (z.bmod (2 * k + 1)) ^ 2 ≤ (k : ℤ) ^ 2 := by
  have hlo := Int.le_bmod (x := z) (m := 2 * k + 1) (by omega)
  have hhi := Int.bmod_lt (x := z) (m := 2 * k + 1) (by omega)
  norm_num [Nat.cast_add, Nat.cast_mul] at hlo hhi
  have hdivlo : (2 * (k : ℤ) + 1) / 2 = k := by omega
  have hdivhi : (2 * (k : ℤ) + 1 + 1) / 2 = k + 1 := by omega
  rw [hdivlo] at hlo
  rw [hdivhi] at hhi
  nlinarith

end MetaMathlibExt
