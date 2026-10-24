import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourDynamicGradeCount_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCount.lean)
-/
@[path]
private lemma sixVertexFourByFourDynamicGradeCount_certificate_eq
  {sector : Fin 5}
  {totalC : Fin 17} :
-- imply
  sixVertexFourDynamicGradeCount sector totalC.val = sixVertexFourByFourGradeCountTable sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDynamicGradeCount_certificate sector totalC

/--
[sixVertexFourByFourRowCycleGradeCount_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCount.lean)
-/
@[path]
private lemma sixVertexFourByFourRowCycleGradeCount_certificate_eq
  {sector : Fin 5}
  {totalC : Fin 17} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCount sixVertexFourByFourTorus sector totalC.val = sixVertexFourByFourGradeCountTable sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowCycleGradeCount_certificate sector totalC


-- created on 2026-10-23
