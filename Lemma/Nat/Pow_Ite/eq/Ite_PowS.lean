import Lemma.Bool.BFn_Ite.eq.Ite_BFnS
open Bool


@[main]
private lemma main
  [Decidable p]
  [HPow α β γ]
  {c : α}
  {a b : β} :
-- imply
  c ^ (if p then
    a
  else
    b) = if p then
    c ^ a
  else
    c ^ b := by
-- proof
  apply BFn_Ite.eq.Ite_BFnS HPow.hPow


-- created on 2025-04-27
-- updated on 2025-04-30
