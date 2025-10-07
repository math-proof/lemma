import Lemma.Bool.ImpEq.of.ImpEq
open Bool


@[main]
private lemma subst
  {a b : α}
  {p : α → Prop} :
-- imply
  (a = b → p a) ↔ (a = b → p b) := by
-- proof
  constructor
  apply ImpEq.of.ImpEq.subst
  rw [Eq.comm (a := a) (b := b)]
  apply ImpEq.of.ImpEq.subst


-- created on 2025-01-12
-- updated on 2025-06-06
