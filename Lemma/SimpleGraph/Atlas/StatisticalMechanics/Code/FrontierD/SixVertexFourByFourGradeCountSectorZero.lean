import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorZero
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_sectorZero_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCountSectorZero.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_sectorZero_certificate_eq :
-- imply
  ∀ totalC : Fin 17, sixVertexFourDynamicGradeCount sixVertexFourByFourSectorZero totalC.val = sixVertexFourByFourGradeCountTable 0 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_sectorZero_certificate


-- created on 2026-10-23
