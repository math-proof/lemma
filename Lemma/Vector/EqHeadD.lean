import sympy.vector.vector
import sympy.Basic


@[path]
private lemma main
-- given
  (s : List.Vector α 0)
  (default : α) :
-- imply
  s.headD default = default := by
-- proof
  match s with
  | .nil => rfl


-- created on 2024-07-01
-- updated on 2025-06-29
