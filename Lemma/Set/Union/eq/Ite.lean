import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {s A B : Set α} :
-- imply
  s ∪ (if p then
    A
  else
    B) = if p then
    s ∪ A
  else
    s ∪ B := by
-- proof
  if hc : p then
    simp [hc]
  else
    simp [hc]


-- created on 2021-01-24
-- updated on 2026-10-26
