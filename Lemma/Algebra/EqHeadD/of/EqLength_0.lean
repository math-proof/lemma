import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length = 0)
  (default : α) :
-- imply
  s.headD default = default := by
-- proof
  match s with
  | .nil =>
    simp
  | .cons hd tl =>
    contradiction


-- created on 2025-05-04
