/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3


namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


namespace FiniteCellularGraphEmbedding

theorem ribbonSystem_boundaryParity
    (embedding : FiniteCellularGraphEmbedding G) :
    forall edges : Finset (finiteGraphEdge G),
      (edgesᶜ.card + embedding.ribbonSystem.boundaryComponents edges) % 2 =
        embedding.faceCount % 2 :=
  embedding.cellularDualData.boundaryParity


theorem isoradialCritical_subgraphSum_duality
    (embedding : FiniteCellularGraphEmbedding G)
    (character : forall F : Finset (finiteGraphEdge G),
      Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset (finiteGraphEdge G))
      (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)),
        character F boundary ≠ 0)
    (htotal : forall F : Finset (finiteGraphEdge G),
      ∏ boundary, character F boundary = 1)
    (theta : finiteGraphEdge G -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    kwDualSubgraphSum
        (dualRibbonBoundaryCharacterCoefficient
          embedding.ribbonSystem character)
        (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge)) =
      (-1 : Complex) ^ embedding.faceCount *
        ((∏ edge : finiteGraphEdge G,
            isoradialCriticalMu (theta edge))⁻¹ *
          kwDualSubgraphSum
            (ribbonBoundaryCharacterCoefficient
              embedding.ribbonSystem character)
            (fun edge => isoradialCriticalMu (theta edge))) := by
  exact cellularRibbon_isoradialCritical_subgraphSum_duality
    embedding.ribbonSystem embedding.cellularDualData character
      hcharacter htotal theta htheta htheta'

end FiniteCellularGraphEmbedding
end StatMech.FrontierA
