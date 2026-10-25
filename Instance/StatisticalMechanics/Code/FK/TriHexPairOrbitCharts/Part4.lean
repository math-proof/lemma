/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part13
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


instance (s : TriangularPairShape) :
    Decidable (IsTriangularEdgePairShape s) := by
  unfold IsTriangularEdgePairShape
  infer_instance

instance (s : HexagonalPairShape) :
    Decidable (IsHexagonalEdgePairShape s) := by
  unfold IsHexagonalEdgePairShape
  infer_instance

end StatMech.FK.PeriodicPlanar
