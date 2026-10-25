/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Structure.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding


namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


namespace FiniteCellularGraphEmbedding

noncomputable def ribbonSystem (embedding : FiniteCellularGraphEmbedding G) :
    RibbonPermutationSystem (finiteGraphEdge G) G.Dart where
  rotation := embedding.rotation
  edgeFlip := finiteGraphEdge.edgeFlip G
  edgeFlip_isSwap := finiteGraphEdge.edgeFlip_isSwap G
  edgeFlip_commute := by
    intro edge edge' hne
    exact finiteGraphEdge.edgeFlip_commute G hne


noncomputable def cellularDualData
    (embedding : FiniteCellularGraphEmbedding G) :
    CellularRibbonDualData embedding.ribbonSystem where
  primalVertexCount := Fintype.card V
  dualVertexCount := embedding.faceCount
  genus := embedding.genus
  rotationCycles_eq_primalVertexCount :=
    embedding.rotationCycles_eq_vertices
  cellularEuler := by
    simpa using embedding.cellularEuler

end FiniteCellularGraphEmbedding
end StatMech.FrontierA
