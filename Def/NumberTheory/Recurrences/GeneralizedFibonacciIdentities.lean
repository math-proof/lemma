/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean -/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Int.Star

@[expose] public section

namespace MetaMathlibExt

/-- The `p`-Fibonacci sequence `0, 1, p, p ^ 2 + 1, …`. -/
def pFibonacci {R : Type*} [CommRing R] (p : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => p * pFibonacci p (n + 1) + pFibonacci p n

end MetaMathlibExt
