import Mathlib
import Def.Analysis.Tools.ExistsUnique.Part2


theorem Subsingleton.choose_spec {α: Sort*} [hs: Subsingleton α] [Nonempty α] (x:α) : x = hs.choose := Subsingleton.elim _ _

/-- The equivalence between {name}`ExistsUnique` and {name}`Subsingleton`/{name}`Nonempty` does not require choice. -/
theorem ExistsUnique.iff_subsingleton_nonempty  {α: Sort*} {p: α → Prop} :
  (∃! x, p x) ↔ (Subsingleton {x // p x} ∧ Nonempty {x // p x}) := by
  constructor
  · intro h; obtain ⟨ x₀, hx₀ ⟩ := h.exists
    refine ⟨ ⟨ ?_ ⟩, ⟨ _, hx₀ ⟩⟩
    intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
    exact (Subtype.mk.injEq _ _ _ _).symm ▸ (h.unique hx hy)
  intro ⟨ hsing, ⟨ x₀, hx₀ ⟩ ⟩
  apply ExistsUnique.intro _ hx₀; intro y hy
  exact Subtype.mk.injEq _ _ _ _ ▸ (hsing.elim ⟨ _, hy ⟩ ⟨ _, hx₀ ⟩)

