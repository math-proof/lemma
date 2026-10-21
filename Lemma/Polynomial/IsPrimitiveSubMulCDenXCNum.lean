import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_rat_linear_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (q : ℚ) :
-- imply
  (C (q.den : ℤ) * X - C q.num).IsPrimitive := by
-- proof
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro a ha
  have hall := (C_dvd_iff_dvd_coeff a _).mp ha
  have hanum : a ∣ q.num := by
    have h := hall 0
    simp only [coeff_sub, coeff_C_mul_X, coeff_C] at h
    norm_num at h
    exact h
  have haden : a ∣ (q.den : ℤ) := by
    have h := hall 1
    simp only [coeff_sub, coeff_C_mul_X, coeff_C] at h
    norm_num at h
    exact h
  have hanum' : a.natAbs ∣ q.num.natAbs := Int.natAbs_dvd_natAbs.mpr hanum
  have haden' : a.natAbs ∣ q.den := by
    simpa using (Int.natAbs_dvd_natAbs.mpr haden)
  apply Int.isUnit_iff_natAbs_eq.mpr
  exact Nat.dvd_one.mp
    ((Nat.dvd_gcd hanum' haden').trans (by rw [q.reduced.gcd_eq_one]))


-- created on 2026-10-21
