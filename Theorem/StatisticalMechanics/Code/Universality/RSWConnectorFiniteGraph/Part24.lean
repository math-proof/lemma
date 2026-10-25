/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorOuterFaceProjection_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterFaceProjection gamma gamma'
        (rlc_connectorOuterFace gamma gamma' C) = C :=
  rfl


theorem rlc_connectorOuterSpoke_adj_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorOuterDualVertex gamma gamma')
    (hx : ¬RlcConnectorOuterIsFace gamma gamma' x) :
    (rlc_connectorOuterSpokeGraph gamma gamma').Adj x
      (rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
  refine ⟨?_, rfl, Or.inr trivial⟩
  intro h
  rw [h] at hx
  exact hx trivial


end
end StatMech.Universality
