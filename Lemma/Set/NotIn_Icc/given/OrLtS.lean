import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {e a b : α}
-- given
  (h : e ∉ Icc a b) :
-- imply
  e < a ∨ b < e :=
-- proof
  if h₁ : e < a then
    Or.inl h₁
  else if h₂ : b < e then
    Or.inr h₂
  else
    False.elim (h ⟨le_of_not_gt h₁, le_of_not_gt h₂⟩)


-- created on 2026-10-03
