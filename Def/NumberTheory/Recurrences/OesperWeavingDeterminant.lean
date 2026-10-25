/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/OesperWeavingDeterminant.lean -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith.Frontend


namespace MetaMathlibExt

open scoped BigOperators Matrix

def Cfun : Nat → Int := fun j => Finset.sum (Finset.Icc 1 j)
  (fun i => (-1 : Int) ^ (i + 1) * Nat.fib i)

def Mmat : Matrix (Fin 3) (Fin 3) Int := !![2, -1, 0; 0, 0, 1; -1, 0, 2]

end MetaMathlibExt
