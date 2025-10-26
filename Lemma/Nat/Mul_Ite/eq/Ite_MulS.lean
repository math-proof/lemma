import Lemma.Bool.BFn_Ite.eq.Ite_BFnS
open Bool


@[main]
private lemma main
  [Decidable p]
  [Mul α]
  {a b c : α} :
-- imply
  c * (if p then
    a
  else
    b) = if p then
    c * a
  else
    c * b := by
-- proof
  apply BFn_Ite.eq.Ite_BFnS (f := (· * · : α → α → α))


-- created on 2025-04-12
