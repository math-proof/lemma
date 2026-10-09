import sympy.Basic


@[path]
private lemma baseset
  {B : Set α}
  {p : α → Prop} :
-- imply
  ∀ x ∈ {x ∈ B | p x}, p x ∧ x ∈ B :=
-- proof
  fun _ h => ⟨h.2, h.1⟩


-- created on 2020-08-12
