import sympy.core.relational
import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.IffNotNot
open Logic


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
  rw [Or.comm]
  assumption


-- created on 2025-04-17
