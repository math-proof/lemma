import sympy.Basic


@[path]
private lemma domain_defined
  {D : Set α}
  {i : α}
-- given
  (h₀ : p ∨ i ∉ D)
  (h₁ : i ∈ D) :
-- imply
  p :=
-- proof
  h₀.resolve_right (not_not.mpr h₁)


-- created on 2019-03-16
