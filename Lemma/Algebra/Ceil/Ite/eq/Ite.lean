import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b : α} :
-- imply
  ⌈if p then a else b⌉ = if p then ⌈a⌉ else ⌈b⌉ := by
-- proof
  split_ifs <;> rfl


-- created on 2018-11-02
-- updated on 2026-08-20
