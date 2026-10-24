import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorOne
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_sectorOne_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCountSectorOne.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_sectorOne_certificate_eq :
-- imply
  ∀ totalC : Fin 17, sixVertexFourDynamicGradeCount sixVertexFourByFourSectorOne totalC.val = sixVertexFourByFourGradeCountTable 1 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_sectorOne_certificate


-- created on 2026-10-23
