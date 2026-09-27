import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a : α}
-- given
  (h₀ : -x ≤ a)
  (h₁ : x ≤ a) :
-- imply
  |x| ≤ a :=
-- proof
  abs_le.mpr ⟨neg_le.mp h₀, h₁⟩


-- created on 2026-09-26
