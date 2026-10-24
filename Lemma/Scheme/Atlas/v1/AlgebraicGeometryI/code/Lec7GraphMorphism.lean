import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec7GraphMorphism


/--
[graphOfMorphism_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7GraphMorphism.lean)
-/
@[path]
lemma graphOfMorphism_eq_range
  {f : X → Y} :
-- imply
  graphOfMorphism f = Set.range (fun x => (x, f x)) := by
-- proof
  ext ⟨x, y⟩
  simp only [graphOfMorphism, Set.mem_setOf_eq, Set.mem_range, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨x, rfl, h.symm⟩
  · rintro ⟨a, rfl, rfl⟩; rfl


-- created on 2026-10-23
