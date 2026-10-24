import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Cor21Genus1Group
open WeierstrassCurve.Affine in


/--
[isSmooth_Genus1_of_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Cor21Genus1Group.lean)
-/
@[path]
lemma isSmooth_Genus1_of_isElliptic
  [Field F]
  {W : WeierstrassCurve.Affine F}
  [hW : W.IsElliptic] :
-- imply
  IsSmooth_Genus1 W :=
-- proof
  ⟨hW, rfl⟩


-- created on 2026-10-23
