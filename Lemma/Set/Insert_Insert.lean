import sympy.Basic


@[main]
private lemma Comm
  {a b : α}
  {s : Set α} :
-- imply
  insert a (insert b s) = insert b (insert a s) :=
-- proof
  Set.insert_comm a b s


-- created on 2026-08-31
