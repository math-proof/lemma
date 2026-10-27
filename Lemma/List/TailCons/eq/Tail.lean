import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (l : List α)
  (a : α) :
-- imply
  (a :: l.tail).tail = l.tail :=
-- proof
  rfl


-- created on 2024-07-01
-- updated on 2026-10-26
