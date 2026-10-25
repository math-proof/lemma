/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[reducible] noncomputable def rlc_connectorCrossedBoxPlanar (n : Int) :
    Lattice.PlanarZ2Subgraph where
  V := rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2)
  finV := (rect_finite (-2 * n - 1) (2 * n + 1) (-n) (n + 2)).to_subtype
  decV := Classical.decEq _
  G := (hypercubicLattice 2).induce
    (rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2))
  emb := Function.Embedding.subtype _
  isSub := fun _ _ hxy => hxy


end
end StatMech.Universality
