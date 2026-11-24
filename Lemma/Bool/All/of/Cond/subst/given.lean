import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ m < n + 1, p m) :
-- imply
  ∀ x < n + 1, p x :=
-- proof
  h




-- created on 2018-12-13
-- updated on 2026-11-24
