/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PolynomialTL1.lean -/


import Def.NumberTheory.PolynomialTL1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Def.MathlibExtTest.NumberTheory.PolynomialTL1


namespace MetaMathlibExt

open Polynomial

example : IsPolyTFamily concreteS concreteT := by
  constructor
  · simp [concreteT]
  constructor
  · intro l hl
    have hl0 : l ≠ 0 := by omega
    simp [concreteT, hl0]
  · intro l hl x hx hx4
    have hl0 : l ≠ 0 := by omega
    have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have h4x : 4 - x ≠ 0 := by linarith
    rw [show concreteT l = X ^ (l - 1) by simp [concreteT, hl0]]
    apply HasDerivAt.congr_deriv
      (((Real.hasDerivAt_sqrt hx.ne').const_mul 2).mul
        ((X ^ (l - 1)).hasDerivAt_aeval x))
    simp only [TIntegrand, concreteS, map_sub, map_mul, map_pow,
      aeval_C, aeval_X]
    simp only [concreteT, hl0, if_false]
    field_simp
    rw [Real.sq_sqrt hx.le]
    simp
    ring

end MetaMathlibExt
