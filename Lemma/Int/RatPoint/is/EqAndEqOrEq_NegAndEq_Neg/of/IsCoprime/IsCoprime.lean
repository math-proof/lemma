import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_CuspSpace
import Lemma.Definitions.Def_ModularCurve_GenusNumerics
import Lemma.Int.P2MUtil

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups
open ModularCurve ModularCurve.CuspSpace

/--
[ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.lean)
-/
@[path]
private lemma main
  {a c a' c' : ℤ}
-- given
  (h : IsCoprime a c)
  (h' : IsCoprime a' c') :
-- imply
  ModularCurve.ratPoint a c = ModularCurve.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by
  constructor
  ·
    intro heq
    rcases eq_or_ne c 0 with rfl | hc
    ·
      have hc' : c' = 0 := by
-- proof
        rw [ratPoint_zero_right] at heq
        exact ratPoint_eq_infty_iff.mp heq.symm
      subst hc'
      have hu : IsUnit a := isCoprime_zero_right.mp h
      have hu' : IsUnit a' := isCoprime_zero_right.mp h'
      rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
          rcases Int.isUnit_iff.mp hu' with rfl | rfl <;>
        norm_num
    ·
      have hc' : c' ≠ 0 := by
        intro h0
        rw [h0, ratPoint_zero_right, ratPoint_eq_infty_iff] at heq
        exact hc heq
      have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
      have hcQ' : (c' : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc'
      rw [ratPoint_of_ne_zero _ hc, ratPoint_of_ne_zero _ hc', OnePoint.coe_eq_coe,
        div_eq_div_iff hcQ hcQ'] at heq
      have hZ : a * c' = a' * c := by exact_mod_cast heq
      have h1 : c ∣ c' := h.symm.dvd_of_dvd_mul_left ⟨a', by linear_combination hZ⟩
      have h2 : c' ∣ c := h'.symm.dvd_of_dvd_mul_left ⟨a, by linear_combination - hZ⟩
      obtain ⟨u, hu⟩ := h1
      obtain ⟨v, hv⟩ := h2
      have huv : u * v = 1 := by
        have h3 : c * (u * v) = c * 1 := by
          rw [mul_one, ← mul_assoc, ← hu, ← hv]
        refine mul_left_cancel₀ hc h3
      rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one v huv) with hu1 | hu1
      ·
        rw [hu1, mul_one] at hu
        rw [hu] at hZ
        exact Or.inl ⟨mul_right_cancel₀ hc hZ, hu.symm⟩
      ·
        rw [hu1, mul_neg_one] at hu
        have hc2 : c = -c' := by rw [hu]; ring
        have h4 : a * c' = -a' * c' := by
          rw [hc2] at hZ
          linear_combination hZ
        refine Or.inr ⟨mul_right_cancel₀ hc' h4, hc2⟩
  ·
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact ratPoint_neg_neg a' c'


-- created on 2026-10-23
