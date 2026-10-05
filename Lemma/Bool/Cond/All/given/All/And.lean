import sympy.Basic


@[main]
private lemma main
  {B : Set β}
  {c : Prop}
  {g : β → Prop}
-- given
  (hc : c)
  (h : ∀ y ∈ B, g y) :
-- imply
  ∀ y ∈ B, c ∧ g y := by
-- proof
  intro y hy
  exact ⟨hc, h y hy⟩


-- created on 2023-06-06
