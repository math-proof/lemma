import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.Or_Not
open Logic


@[main]
private lemma main
  [DecidableEq α]
-- given
  (a b : α) :
-- imply
  {a} ∩ {b} = if a = b then
  ({a} : Set α)
  else
    ∅ := by
-- proof
  apply BFn_Ite.of.OrAndS
  simp [Singleton]
  simp [Eq.comm]
  apply Or_Not


-- created on 2025-08-02
