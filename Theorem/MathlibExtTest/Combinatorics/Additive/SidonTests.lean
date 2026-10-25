/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/SidonTests.lean -/


import Def.Combinatorics.Additive.Sidon


example {α : Type*} [AddCommMonoid α] (a : α) : Set.IsSidon ({a} : Set α) := by
  intro x hx y hy z hz w hw _
  subst x
  subst y
  subst z
  subst w
  exact Or.inl ⟨rfl, rfl⟩

