import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.QuasiprojectiveSeparated
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuasiprojectiveSeparated


namespace QuasiprojectiveSeparated

/--
[separated_of_openImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QuasiprojectiveSeparated.lean)
-/
@[path]
lemma separated_of_openImmersion
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsOpenImmersion f]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

end QuasiprojectiveSeparated

namespace QuasiprojectiveSeparated

/--
[separated_of_closedImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QuasiprojectiveSeparated.lean)
-/
@[path]
lemma separated_of_closedImmersion
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsClosedImmersion f]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

end QuasiprojectiveSeparated

namespace QuasiprojectiveSeparated

/--
[separated_of_locally_closed_immersion_to_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QuasiprojectiveSeparated.lean)
-/
@[path]
lemma separated_of_locally_closed_immersion_to_separated
  {X Z Y : Scheme.{u}}
  {f : X ⟶ Z}
  {g : Z ⟶ Y}
  [IsClosedImmersion f]
  [IsOpenImmersion g]
  [Y.IsSeparated] :
-- imply
  X.IsSeparated := by
-- proof
  have : Z.IsSeparated := separated_of_openImmersion g
  exact separated_of_closedImmersion f

end QuasiprojectiveSeparated

namespace QuasiprojectiveSeparated

/--
[quasiprojective_isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QuasiprojectiveSeparated.lean)
-/
@[path]
lemma quasiprojective_isSeparated
  {X : Scheme.{u}}
  [IsQuasiProjective X] :
-- imply
  X.IsSeparated := by
-- proof
  obtain ⟨σ, A, hCR, hSL, hASG, 𝒜, hGR, Z, f, g, hf, hg⟩ :=
    IsQuasiProjective.exists_locally_closed_immersion (X := X)
  have hProj : (Proj 𝒜).IsSeparated := inferInstance
  exact @separated_of_locally_closed_immersion_to_separated _ Z (Proj 𝒜) f g hf hg hProj

end QuasiprojectiveSeparated


-- created on 2026-10-23
