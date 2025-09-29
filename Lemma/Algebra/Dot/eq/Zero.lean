import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
  {x y : List.Vector α 0} :
-- imply
  x ⬝ y = 0 := by
-- proof
  simp [Dot.dot]
  match x, y with
  | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
    simp at xProperty yProperty
    simp [List.Vector.dot, xProperty, yProperty]


-- created on 2024-07-01
-- updated on 2025-05-03
