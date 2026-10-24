import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorTwo
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_sectorTwo_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCountSectorTwo.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_sectorTwo_certificate_eq :
-- imply
  ∀ totalC : Fin 17, sixVertexFourDynamicGradeCount sixVertexFourByFourSectorTwo totalC.val = sixVertexFourByFourGradeCountTable 2 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_sectorTwo_certificate


-- created on 2026-10-23
