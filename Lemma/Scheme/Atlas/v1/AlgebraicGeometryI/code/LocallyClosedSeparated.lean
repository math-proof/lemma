import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory Limits


namespace AlgebraicGeometry

/--
[isSeparated_of_isImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyClosedSeparated.lean)
-/
@[path]
lemma isSeparated_of_isImmersion
  {Z X : Scheme.{u}}
  {f : Z ⟶ X}
  [IsImmersion f]
  [X.IsSeparated] :
-- imply
  Z.IsSeparated := by
-- proof
  constructor
  rw [show terminal.from Z = f ≫ terminal.from X from terminal.hom_ext _ _]
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[isSeparated_comp_of_isImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyClosedSeparated.lean)
-/
@[path]
lemma isSeparated_comp_of_isImmersion
  {Z X S : Scheme.{u}}
  {f : Z ⟶ X}
  {g : X ⟶ S}
  [IsImmersion f]
  [IsSeparated g] :
-- imply
  IsSeparated (f ≫ g) := by
-- proof
  infer_instance

end AlgebraicGeometry


-- created on 2026-10-23
