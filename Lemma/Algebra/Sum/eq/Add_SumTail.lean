import Lemma.Algebra.SumCons.eq.Add_Sum
import Lemma.Algebra.Sum.eq.Zero
import Lemma.Algebra.EqHeadD
import Lemma.Algebra.EqHeadDCons
open Algebra


@[main]
private lemma main
  [AddMonoid α]
  {l : List.Vector α n} :
-- imply
  l.sum = (l.headD 0) + l.tail.sum := by
-- proof
  match n with
  | .zero =>
    simp [EqHeadD, Sum.eq.Zero]
  | .succ n =>
    have h : l = l.head ::ᵥ l.tail := by simp
    rw [h]
    rw [
      SumCons.eq.Add_Sum.vector,
      EqHeadDCons
    ]
    simp


-- created on 2024-07-01
