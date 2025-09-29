import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Add α]
  {a b c : α} :
-- imply
  (if p then
    c + a
  else
    c + b) = c + if p then
    a
  else
    b := by
-- proof
  split_ifs with h <;> rfl


-- created on 2025-04-26
-- updated on 2025-05-14
