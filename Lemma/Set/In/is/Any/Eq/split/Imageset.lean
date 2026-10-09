import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.In.is.Any.Eq.split.Imageset |
| mp | Set.Any.Eq.split.Imageset.of.In |
| mpr | Set.In.of.Any.Eq.split.Imageset |
-/
@[path, mp, mpr]
private lemma main
  {S : Set α}
  {y : β}
  {f : α → β} :
-- imply
  y ∈ f '' S ↔ ∃ x ∈ S, y = f x := by
-- proof
  constructor <;>
  ·
    intro h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, hx, rfl⟩


-- created on 2026-10-07
