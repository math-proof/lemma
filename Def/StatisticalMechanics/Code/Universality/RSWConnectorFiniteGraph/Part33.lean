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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorOuterSpokeGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorOuterDualVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_connectorOuterFaceProjection gamma gamma' x =
      rlc_connectorOuterFaceProjection gamma gamma' y ∧
    (RlcConnectorOuterIsFace gamma gamma' x ∨
      RlcConnectorOuterIsFace gamma gamma' y)
  symm := by
    constructor
    rintro x y ⟨hne, hface, hghost⟩
    exact ⟨hne.symm, hface.symm, hghost.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.Universality
