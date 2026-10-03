import sympy.Basic


@[main]
private lemma main
  {c : Prop} [Decidable c]
  {x y : α}
  {P : α → Prop}
-- given
  (h : P (if c then x else y))
  (h₁ : c) :
-- imply
  P x ∧ c := by
-- proof
  exact ⟨by rwa [if_pos h₁] at h, h₁⟩


-- created on 2018-11-04
