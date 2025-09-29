import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List.Vector α 0} :
-- imply
  s.sum = 0 := by
-- proof
  match s with
  | ⟨v, property⟩ =>
    simp at property
    simp [List.Vector.sum, property]


-- created on 2024-07-01
