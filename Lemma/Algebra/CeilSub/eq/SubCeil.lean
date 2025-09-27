import Lemma.Basic


@[main]
private lemma nat
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d := by
-- proof
  simp


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d :=
-- proof
  Int.ceil_sub_intCast x d




-- created on 2025-05-04
