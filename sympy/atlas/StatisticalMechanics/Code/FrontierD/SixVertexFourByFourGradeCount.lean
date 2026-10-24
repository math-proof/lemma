/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourGradeCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorZero
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorOne
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorTwo
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorThree
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCountSectorFour

namespace StatMech.FrontierD

theorem sixVertexFourByFourDynamicGradeCount_certificate
    (sector : Fin 5) (totalC : Fin 17) :
    sixVertexFourDynamicGradeCount sector totalC.val =
      sixVertexFourByFourGradeCountTable sector totalC := by
  fin_cases sector
  · exact sixVertexFourByFourDynamicGradeCount_sectorZero_certificate totalC
  · exact sixVertexFourByFourDynamicGradeCount_sectorOne_certificate totalC
  · exact sixVertexFourByFourDynamicGradeCount_sectorTwo_certificate totalC
  · exact sixVertexFourByFourDynamicGradeCount_sectorThree_certificate totalC
  · exact sixVertexFourByFourDynamicGradeCount_sectorFour_certificate totalC

theorem sixVertexFourByFourRowCycleGradeCount_certificate
    (sector : Fin 5) (totalC : Fin 17) :
    sixVertexMarkedSectorRowCycleGradeCount
        sixVertexFourByFourTorus sector totalC.val =
      sixVertexFourByFourGradeCountTable sector totalC := by
  rw [← sixVertexMarkedSectorRowCycleGradeCountExecutable_eq]
  rw [sixVertexFourGradeCountExecutable_eq_dynamic]
  exact sixVertexFourByFourDynamicGradeCount_certificate sector totalC

end StatMech.FrontierD
