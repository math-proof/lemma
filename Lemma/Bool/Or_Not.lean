import Initialize.Tactic.Attr.Basic


/--
law of excluded middle
-/
@[path]
private lemma main
-- given
  (p : Prop) :
-- imply
  p ∨ ¬p :=
-- proof
  Classical.em p


-- created on 2024-07-01
-- updated on 2026-10-26
