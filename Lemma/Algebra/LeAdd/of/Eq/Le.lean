import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b x y : α}
-- given
  (h₀ : a = x)
  (h₁ : y ≤ b) :
-- imply
  a + y ≤ x + b := by
-- proof
  rw [h₀]
  simpa [add_comm] using add_le_add_left h₁ x


-- created on 2018-10-29
-- updated on 2026-08-20
