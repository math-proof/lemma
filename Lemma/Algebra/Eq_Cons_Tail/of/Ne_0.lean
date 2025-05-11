import Lemma.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s = s[0] :: s.tail := by
-- proof
  match s with
  | .nil =>
    -- If s is nil, then its length is 0, which contradicts h.
    contradiction
  | .cons head tail =>
    -- If s is cons head tail, then we need to show that s = head :: tail.
    -- This is trivially true by definition of cons.
    rfl


-- created on 2024-07-01
-- updated on 2025-05-11
