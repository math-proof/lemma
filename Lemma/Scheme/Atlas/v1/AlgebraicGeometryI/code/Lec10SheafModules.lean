import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec10SheafModules
open AlgebraicGeometry


/--
[sheafOfOXModules_eq_sheafOfModules](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheafModules.lean)
-/
@[path]
lemma sheafOfOXModules_eq_sheafOfModules
  {X : Scheme.{u}} :
-- imply
  SheafOfOXModules X = SheafOfModules.{u} X.ringCatSheaf :=
-- proof
  rfl


-- created on 2026-10-23
