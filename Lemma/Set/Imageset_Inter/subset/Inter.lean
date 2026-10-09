import sympy.Basic


@[path]
private lemma main
  {ι α : Type*}
  {f : ι → α}
  {A B : Set ι} :
-- imply
  f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
-- proof
  intro y hy
  obtain ⟨x, ⟨ha, hb⟩, rfl⟩ := hy
  exact ⟨Set.mem_image_of_mem f ha, Set.mem_image_of_mem f hb⟩


-- created on 2021-04-26
