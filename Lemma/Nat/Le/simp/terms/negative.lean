import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (x y a b : ℤ) :
-- imply
  x - a ≤ y - b ↔ x + b ≤ y + a := by
-- proof
  omega


-- created on 2021-09-14
-- updated on 2026-10-26
