/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators

namespace MetaMathlibExt

private noncomputable def tauCube : ArithmeticFunction ℕ :=
  { toFun := fun n => (n.divisors.card) ^ 3
    map_zero' := by simp }

private noncomputable def F : ArithmeticFunction ℕ :=
  ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta
private noncomputable def G : ArithmeticFunction ℕ :=
  tauCube * ArithmeticFunction.zeta

private noncomputable def Fsq : ArithmeticFunction ℕ :=
  { toFun := fun n => (F n) ^ 2
    map_zero' := by simp }
end MetaMathlibExt
