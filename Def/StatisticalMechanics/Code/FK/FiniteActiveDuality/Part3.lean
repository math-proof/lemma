/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteActiveDuality.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


def ActiveFreeWiredEulerIdentity
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet) : Prop :=
  ∀ omega : ConfigSpace G.edgeSet,
    Fintype.card V +
        numClustersWired H boundary
          (extendActive H (activeDualConfig G H edgeDual omega)) =
      activeOpenCount G omega +
        numClusters G (extendActive G omega) + 1


end
end StatMech.FK
