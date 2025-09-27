import sympy.core.power
import Lemma.Algebra.Sum_Square.ge.Zero
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
  {a b : ι → α} :
-- imply
  ∑ i ∈ s, (a i * x + b i)² ≥ 0 := by
-- proof
  apply Sum_Square.ge.Zero (a := fun i => a i * x + b i)


-- created on 2025-04-06
