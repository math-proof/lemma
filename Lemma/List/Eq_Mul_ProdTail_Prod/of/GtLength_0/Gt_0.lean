import Lemma.Algebra.Ne.of.Gt
import Lemma.List.Prod.eq.Mul_ProdTail.of.Ne_0.NeLength_0
open Algebra List


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h₀: shape.length > 0)
  (h₁: shape[0] > 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  have h₀' := Ne.of.Gt h₀
  have h₁' := Ne.of.Gt h₁
  apply Prod.eq.Mul_ProdTail.of.Ne_0.NeLength_0 h₀' h₁'


-- created on 2024-07-01
