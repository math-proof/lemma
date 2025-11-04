import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > 0)
  (h_i : i > 0) :
-- imply
  s.take i = s[0] :: s.tail.take (i - 1) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    cases i <;>
      grind


-- created on 2025-07-05
-- updated on 2025-07-06
