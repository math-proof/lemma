import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorThree
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_sectorThree_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCountSectorThree.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_sectorThree_certificate_eq :
-- imply
  ∀ totalC : Fin 17, sixVertexFourDynamicGradeCount sixVertexFourByFourSectorThree totalC.val = sixVertexFourByFourGradeCountTable 3 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_sectorThree_certificate


-- created on 2026-10-23
