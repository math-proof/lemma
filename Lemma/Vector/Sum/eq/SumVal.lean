import sympy.vector.vector


@[path]
private lemma main
  [Add α] [Zero α]
-- given
  (a : List.Vector α n) :
-- imply
  a.sum = a.val.sum := by
-- proof
  rfl


-- created on 2026-07-22
