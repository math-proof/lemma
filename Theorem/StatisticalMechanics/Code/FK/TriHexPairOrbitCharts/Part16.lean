/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part18
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triHexPairShapeOffset_edge (i : Fin 3) :
    triangularEdgePairBase i + triHexPairShapeOffset
      (triangularEdgePairShape i) =
        (triHexIndexEquiv (0, i)).1 := by
  fin_cases i <;>
    simp [triangularEdgePairBase, triangularEdgePairShape,
      triangularPairNormal, triangularStep, siteLexNonnegative,
      triHexPairShapeOffset, triHexIndexEquiv, funext_iff]
  all_goals
    intro h
    have h1 := congrArg (fun s : TriangularPairShape => s.1 1) h
    norm_num at h1


end StatMech.FK.PeriodicPlanar
