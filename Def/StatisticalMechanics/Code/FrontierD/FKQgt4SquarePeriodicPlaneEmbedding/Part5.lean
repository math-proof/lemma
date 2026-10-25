/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

noncomputable def squarePeriodicPlaneEmbeddingAt (offset : Complex) :
    PeriodicPlaneEmbedding square where
  vertex := squareOffsetVertex offset
  period := squareComplexPeriod
  period_injective := by
    intro x y hxy
    exact squareComplexPoint_injective hxy
  coordinates := squareComplexCoordinates
  coordinates_period := by
    intro z i
    fin_cases i <;> simp [squareComplexCoordinates, squareComplexPeriod]
  vertex_shift := squareOffsetVertex_shift offset
  proper := squareOffsetVertex_proper offset
  edgeArc := squareOffsetEdgeArc offset
  edgeArc_injective := squareOffsetEdgeArc_injective offset
  edgeArc_symm := squareOffsetEdgeArc_symm offset
  edgeArc_shift := squareOffsetEdgeArc_shift offset
  edgeArc_intersection := squareOffsetEdgeArc_intersection offset
  edgeArc_disjoint := squareOffsetEdgeArc_disjoint offset
  edgeArc_locallyFinite := squareOffsetEdgeArc_locallyFinite offset

end
end StatMech.FrontierD
