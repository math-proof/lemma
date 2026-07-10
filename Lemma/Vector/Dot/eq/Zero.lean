import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (x y : List.Vector α 0) :
-- imply
  x @ y = 0 := by
-- proof
  simp [Dot.dot]
  match x, y with
  | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
    simp at xProperty yProperty
    simp [List.Vector.dot, xProperty, yProperty]


-- created on 2024-07-01
-- updated on 2026-07-10
