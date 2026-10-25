import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorFour
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_sectorFour_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCountSectorFour.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_sectorFour_certificate_eq :
-- imply
  ∀ totalC : Fin 17, sixVertexFourDynamicGradeCount 4 totalC.val = sixVertexFourByFourGradeCountTable 4 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_sectorFour_certificate


-- created on 2026-10-23
