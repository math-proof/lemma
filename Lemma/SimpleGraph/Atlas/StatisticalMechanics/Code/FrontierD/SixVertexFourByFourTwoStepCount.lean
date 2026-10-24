import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount
open StatMech StatMech.FrontierD


/--
[sixVertexFourTwoStepCountTable_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoStepCount.lean)
-/
@[path]
private lemma sixVertexFourTwoStepCountTable_certificate_eq :
-- imply
  ∀ start finish : Fin 16, ∀ grade : Fin 9, sixVertexFourTwoStepCountExecutable start finish grade = sixVertexFourTwoStepCountTable start finish grade := by
-- proof
  apply StatMech.FrontierD.sixVertexFourTwoStepCountTable_certificate

/--
[sixVertexFourDynamicGradeCount_zero_test](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoStepCount.lean)
-/
@[path]
private lemma sixVertexFourDynamicGradeCount_zero_test_eq :
-- imply
  sixVertexFourDynamicGradeCount sixVertexFourByFourSectorZero 0 = 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourDynamicGradeCount_zero_test


-- created on 2026-10-23
