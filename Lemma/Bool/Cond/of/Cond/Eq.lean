import sympy.Basic


@[main]
private lemma given
  {c : Prop} [Decidable c]
  {x y : α}
  {P : α → Prop}
-- given
  (h₀ : P x)
  (h₁ : c) :
-- imply
  P (if c then x else y) := by
-- proof
  rwa [if_pos h₁]


-- created on 2018-11-04
