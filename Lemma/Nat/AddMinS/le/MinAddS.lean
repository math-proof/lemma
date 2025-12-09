import sympy.Basic


/--
the triangular inequality for `min` and `+`
-/
@[main]
private lemma main
  [Add α]
  [LinearOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (a b c d : α) :
-- imply
  a ⊓ c + b ⊓ d ≤ (a + b) ⊓ (c + d) :=
-- proof
  min_add_min_le_min_add_add


-- created on 2025-12-08
