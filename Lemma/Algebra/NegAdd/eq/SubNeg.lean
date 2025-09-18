import Lemma.Algebra.Sub.eq.Add_Neg
open Algebra


@[main, comm]
private lemma main
  [SubtractionCommMonoid α]
  {a b : α} :
-- imply
  -(a + b) = -a - b := by
-- proof
  rw [neg_add]
  rw [Add_Neg.eq.Sub]



-- created on 2025-03-30
