module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part84
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredOuterDualConfig_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCollaredOuterDualConfig gamma gamma' tau ≤
      rlc_connectorCollaredOuterMaxConfig gamma gamma' := by
  intro a
  unfold rlc_connectorCollaredOuterMaxConfig
    rlc_connectorCollaredOuterDualConfig
  split
  · rename_i h
    unfold rlc_connectorForceTraceConfig
    split
    · rfl
    · cases tau h.choose.1 <;> simp
  · exact le_rfl

end
end StatMech.Universality
