import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x < 1) :
-- imply
  x = Int.fract x :=
-- proof
  (Int.fract_eq_self.mpr ⟨h₀, h₁⟩).symm


-- created on 2026-09-27
