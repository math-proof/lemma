import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ChowHelperBlowupProjective
open AlgebraicGeometry CategoryTheory Limits ChowHelperBlowupProjective
open immersion `U ↪ Y` with dense image. -/


namespace ChowHelperBlowupProjective

/--
[isBirational_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowHelperBlowupProjective.lean)
-/
@[path]
lemma isBirational_refl
  {X : Scheme.{u}} :
-- imply
  IsBirational X X :=
-- proof
  ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance,
    by have h : Function.Surjective (𝟙 X : X ⟶ X).base := fun x => ⟨x, rfl⟩
      rw [Set.range_eq_univ.mpr h]; exact dense_univ,
    by have h : Function.Surjective (𝟙 X : X ⟶ X).base := fun x => ⟨x, rfl⟩
      rw [Set.range_eq_univ.mpr h]; exact dense_univ⟩

end ChowHelperBlowupProjective

namespace ChowHelperBlowupProjective

/--
[isBirational_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowHelperBlowupProjective.lean)
-/
@[path]
lemma isBirational_symm
  {X Y : Scheme.{u}}
-- given
  (h : IsBirational X Y) :
-- imply
  IsBirational Y X := by
-- proof
  obtain ⟨Z, f, g, hf, hg, hdf, hdg⟩ := h
  exact ⟨Z, g, f, hg, hf, hdg, hdf⟩

end ChowHelperBlowupProjective


-- created on 2026-10-23
