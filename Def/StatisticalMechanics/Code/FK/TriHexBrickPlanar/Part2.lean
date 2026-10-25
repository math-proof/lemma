/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC


def hexagonalBrickEmbedding : HexVertex ↪ Site 2 where
  toFun := hexagonalBrickVertex
  inj' := hexagonalBrickVertex_injective


def triHexPlanarFiniteStarBrickEmbedding (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ Site 2 :=
  (triHexPlanarFiniteStarVertexEmbedding n).trans hexagonalBrickEmbedding


noncomputable def triHexPlanarFiniteStarPlanar (n : Nat) :
    PlanarZ2Subgraph where
  V := TriHexPlanarFiniteStarVertex n
  finV := inferInstance
  decV := inferInstance
  G := triHexPlanarFiniteStarGraph n
  emb := triHexPlanarFiniteStarBrickEmbedding n
  isSub := by
    intro u v huv
    exact hexagonalBrickVertex_adj
      (triHexPlanarFiniteStarGraph_adj_hexagonal n huv)

end StatMech.FK.PeriodicPlanar
