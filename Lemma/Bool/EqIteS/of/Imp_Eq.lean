import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {f : α → α}
  {x a b : α}
-- given
  (h : p → x = a) :
-- imply
  (if p then
    f x
  else
    b) = if p then
    f a
  else
    b := by
-- proof
  split_ifs with h_p
  have h := h h_p
  ·
    subst h
    rfl
  ·
    rfl


-- created on 2025-04-19
