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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_extremalSelectionBadCollarX : RlcConnectorVertex 1 :=
  ⟨![-2, -1], by simp [mem_rect]⟩

def rlc_extremalSelectionBadCollarY : RlcConnectorVertex 1 :=
  ⟨![-2, 0], by simp [mem_rect]⟩


def rlc_connectorVertexToCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n → RlcConnectorCollaredVertex gamma gamma' :=
  fun x => ⟨x.1, Finset.mem_union_left _ (by
    change x.1 ∈ (rect_finite (-2 * n) (2 * n) (-n) n).toFinset
    exact (Set.Finite.mem_toFinset
      (rect_finite (-2 * n) (2 * n) (-n) n)).mpr x.2)⟩

end
end StatMech.Universality
