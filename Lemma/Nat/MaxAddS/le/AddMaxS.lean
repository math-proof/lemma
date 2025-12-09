import sympy.Basic


/--
the triangular inequality for `max` and `+`
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
  (a + b) ⊔ (c + d) ≤ a ⊔ c + b ⊔ d :=
-- proof
  max_add_add_le_max_add_max


-- created on 2025-12-08
