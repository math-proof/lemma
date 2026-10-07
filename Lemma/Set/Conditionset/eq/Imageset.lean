import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {f : α → β}
  {p : β → Prop} :
-- imply
  {y ∈ f '' A | p y} = f '' {x ∈ A | p (f x)} := by
-- proof
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hxA, rfl⟩, hp⟩
    exact ⟨x, ⟨hxA, hp⟩, rfl⟩
  · rintro ⟨x, ⟨hxA, hpf⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, hpf⟩


-- created on 2021-02-04
-- updated on 2023-11-11
