import Initialize.Tactic.Attr.Basic


/--
双否定律: double-negation elimination
-/
@[path]
private lemma main
  {p : Prop} :
-- imply
  ¬¬p ↔ p :=
-- proof
  Classical.not_not


-- created on 2024-07-01
-- updated on 2026-10-26
