import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {A B : α}
-- given
  (h : A = B) :
-- imply
  ({A} : Finset α) = {B} :=
-- proof
  congrArg (fun x : α => ({x} : Finset α)) h


-- created on 2020-07-23
-- updated on 2026-09-07
