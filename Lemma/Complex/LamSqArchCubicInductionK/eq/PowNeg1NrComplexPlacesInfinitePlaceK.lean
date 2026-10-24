import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_LanglandsTunnell_LambdaSquared
open NumberField


/--
[LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K] :
-- imply
  LanglandsTunnell.CubicInduction.lamSqArch K = (-1 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  classical
    have hiff : LanglandsTunnell.CubicInduction.discQ K < 0 ↔ discr K < 0 := by
-- proof
      rw [← LanglandsTunnell.CubicInduction.discr_neg_iff K (integralBasis K), ← coe_discr, Int.cast_lt_zero]
    have hsign : (discr K).sign = (-1) ^ NumberField.InfinitePlace.nrComplexPlaces K := NumberField.sign_discr K
    unfold LanglandsTunnell.CubicInduction.lamSqArch
    if hneg : discr K < 0 then
      rw [ite_eq_left (hiff.mpr hneg)]
      rw [Int.sign_eq_neg_one_of_neg hneg] at hsign
      refine Or.elim (Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K)) ?_ ?_
      ·
        intro h
        rw [h.neg_one_pow] at hsign
        norm_num at hsign
      ·
        intro h
        rw [h.neg_one_pow]
    else
      rw [ite_eq_right (mt hiff.mp hneg)]
      have hpos : 0 < discr K := lt_of_le_of_ne (not_lt.mp hneg) (discr_ne_zero K).symm
      rw [Int.sign_eq_one_of_pos hpos] at hsign
      refine Or.elim (Nat.even_or_odd (NumberField.InfinitePlace.nrComplexPlaces K)) ?_ ?_
      ·
        intro h
        rw [h.neg_one_pow]
      ·
        intro h
        rw [h.neg_one_pow] at hsign
        norm_num at hsign


-- created on 2026-10-23
