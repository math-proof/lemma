import Lemma.Algebra.Ne.of.Gt
import Lemma.List.DivProd.eq.ProdTail.of.NeLength_0.Ne_0
open Algebra List


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s[0] > 0) :
-- imply
  s.tail.prod = s.prod / s[0] :=
-- proof
  DivProd.eq.ProdTail.of.NeLength_0.Ne_0
    (Ne.of.Gt h₀)
    (Ne.of.Gt h₁)


-- created on 2025-07-12
