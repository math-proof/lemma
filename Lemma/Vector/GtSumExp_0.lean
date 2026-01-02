import sympy.vector.functions
import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Finset.Lt0Sum.of.All_Gt_0.Ne_Empty
import Lemma.Finset.Any_In.is.Ne_Empty
open Vector Finset


@[main]
private lemma main
  [ExpPos α] [IsOrderedCancelAddMonoid α]
  [NeZero n]
-- given
  (x : List.Vector α n) :
-- imply
  (exp x).sum > 0 := by
-- proof
  rw [Sum.eq.Sum_Get]
  apply Lt0Sum.of.All_Gt_0.Ne_Empty
  .
    apply Ne_Empty.of.Any_In
    aesop
  .
    simp [Exp.exp]
    intro i
    apply ExpPos.exp_pos


-- created on 2025-10-07
-- updated on 2025-10-08
