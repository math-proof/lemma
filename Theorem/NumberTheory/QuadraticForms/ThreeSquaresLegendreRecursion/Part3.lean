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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part3


namespace MetaMathlibExt

lemma r3leg_zmod_two_parity :
    ∀ a b c d : ZMod 2, a + b + c + d = 0 →
      (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  decide

lemma r3leg_zmod_two_sq (a : ZMod 2) : a ^ 2 = a := by
  revert a
  decide

lemma r3leg_zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

lemma r3leg_eps_norm (e : Quaternion ℤ)
    (h : e = r3legEpsI ∨ e = r3legEpsJ ∨ e = r3legEpsK) :
    Quaternion.normSq e = 2 := by
  rcases h with rfl | rfl | rfl <;>
    simp [Quaternion.normSq_def', r3legEpsI, r3legEpsJ, r3legEpsK]

lemma r3leg_two_dvd_of_cast_eq_zero (z : ℤ) (h : (z : ZMod 2) = 0) :
    (2 : ℤ) ∣ z := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp h

lemma r3leg_even_right_factor (q : Quaternion ℤ)
    (h2 : (2 : ℤ) ∣ Quaternion.normSq q) :
    ∃ e : Quaternion ℤ,
      Quaternion.normSq e = 2 ∧
      (2 : ℤ) ∣ (q * e).re ∧ (2 : ℤ) ∣ (q * e).imI ∧
      (2 : ℤ) ∣ (q * e).imJ ∧ (2 : ℤ) ∣ (q * e).imK := by
  have hn : ((Quaternion.normSq q : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  have hsum : (q.re : ZMod 2) + q.imI + q.imJ + q.imK = 0 := by
    rw [Quaternion.normSq_def'] at hn
    push_cast at hn
    simpa only [r3leg_zmod_two_sq] using hn
  rcases r3leg_zmod_two_parity _ _ _ _ hsum with h | h | h
  · refine ⟨r3legEpsI, r3leg_eps_norm _ (Or.inl rfl), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsI]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
  · refine ⟨r3legEpsJ, r3leg_eps_norm _ (Or.inr (Or.inl rfl)), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsJ]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
  · refine ⟨r3legEpsK, r3leg_eps_norm _ (Or.inr (Or.inr rfl)), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsK]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]

end MetaMathlibExt
