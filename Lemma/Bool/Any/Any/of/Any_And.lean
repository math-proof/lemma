import Lemma.Bool.Any.of.Any_And
open Bool


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ q x) :
-- imply
  (∃ x : α, p x) ∧ (∃ x : α, q x) := by
-- proof
  constructor
  ·
    apply Any.of.Any_And.left h
  ·
    apply Any.of.Any_And h


-- created on 2018-08-23
-- updated on 2026-08-20
