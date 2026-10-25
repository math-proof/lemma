/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedFibonacciIdentities.lean -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.Star
import Lemma.Nat.BinetClosedForm
import Lemma.Nat.Recurrences.HoradamGeneralizedCatalanIdentity


namespace MetaMathlibExt

/-- The `p`-Fibonacci sequence `0, 1, p, p ^ 2 + 1, …`. -/
def pFibonacci {R : Type*} [CommRing R] (p : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => p * pFibonacci p (n + 1) + pFibonacci p n

end MetaMathlibExt
