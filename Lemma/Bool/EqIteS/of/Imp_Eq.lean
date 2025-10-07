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
  -- Split the proof into cases based on the truth value of p
  split_ifs with h_p
  have h := h h_p
  ·
    -- Case 1: p is true
    -- Apply the hypothesis h to get x = a
    subst h
    -- Both sides now simplify to f a, which is equal by reflexivity
    rfl
  ·
  -- Case 2: p is false
  -- Both sides simplify to b, which is equal by reflexivity
    rfl


-- created on 2025-04-19
