import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d := by
-- proof
  simp


-- created on 2025-10-08
