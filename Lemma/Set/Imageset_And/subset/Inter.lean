import sympy.Basic


@[main]
private lemma main
  {ι α : Type*}
  {f : ι → α}
  {p q : ι → Prop} :
-- imply
  f '' {x | p x ∧ q x} ⊆ f '' {x | p x} ∩ f '' {x | q x} := by
-- proof
  intro y hy
  obtain ⟨x, ⟨hp, hq⟩, rfl⟩ := hy
  exact ⟨Set.mem_image_of_mem f hp, Set.mem_image_of_mem f hq⟩


-- created on 2021-04-26
