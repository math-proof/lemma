import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Rat


/--
constructor order of multiplication
-/
@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {k n m : α}
-- given
  (h₀ : k < n * m)
  (h₁ : n > 0) :
-- imply
  k / n < m := by
-- proof
  have := LtDivS.of.Lt.Gt_0 h₀ h₁
  rwa [EqDivMul.of.Ne_0.left] at this
  apply Ne.of.Gt h₁


-- created on 2025-07-06
