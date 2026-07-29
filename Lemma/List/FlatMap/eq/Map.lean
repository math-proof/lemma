import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (f : α → β):
-- imply
  s.flatMap (fun a : α => [f a]) = s.map f := by
-- proof
  induction s with
  | nil =>
    simp
  | cons a s ih =>
    simp [ih]


-- created on 2026-07-28
