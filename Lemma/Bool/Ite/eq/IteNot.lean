import sympy.core.relational
import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Bool.IffNotNot
open Bool


@[main]
private lemma main
  [Decidable p]
  {a b : α} :
-- imply
  (if p then
    a
  else
    b) = if ¬p then
    b
  else
    a := by
-- proof
  denote h_P : P = left
  have := OrAndS.of.BFn_Ite h_P
  rw [← h_P]
  apply BFn_Ite.of.OrAndS
  rw [IffNotNot]
  rwa [Or.comm]


-- created on 2025-04-17
