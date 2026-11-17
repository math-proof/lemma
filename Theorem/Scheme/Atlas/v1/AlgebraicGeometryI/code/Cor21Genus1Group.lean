module

public import Mathlib
public import Def.v1.Atlas.AlgebraicGeometryI.code.Cor21Genus1Group.Part2

public section

open WeierstrassCurve.Affine in


/--
[isSmooth_Genus1_of_isElliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Cor21Genus1Group.lean)
-/
public theorem isSmooth_Genus1_of_isElliptic
  [Field F]
  {W : WeierstrassCurve.Affine F}
  [hW : W.IsElliptic] :
-- imply
  IsSmooth_Genus1 W :=
-- proof
  ⟨hW, rfl⟩


-- created on 2026-10-23
