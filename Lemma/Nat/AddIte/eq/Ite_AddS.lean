import Lemma.Bool.BFnIte.eq.Ite_BFnS
open Bool


@[main]
private lemma main
  [Decidable p]
  [Add α]
  {a b c : α} :
-- imply
  (if p then
    a
  else
    b) + c = if p then
    a + c
  else
    b + c := by
-- proof
  apply BFnIte.eq.Ite_BFnS Add.add


-- created on 2025-04-27
