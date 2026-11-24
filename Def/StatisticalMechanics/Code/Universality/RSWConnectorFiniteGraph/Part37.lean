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
public import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part16
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

def rlc_connectorFourTracePlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorFiniteGraph gamma gamma' ⊔
    rlc_connectorTraceWiring gamma gamma' ⊔
      rlc_connectorReflectedTraceWiring gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    rcases hxy with (hxy | hxy) | hxy
    · exact hxy.1
    · exact hxy.1
    · exact hxy.1


noncomputable def rlc_connectorForceFourTraceConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => if e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset then true
    else if e ∈
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset then false
    else tau e

end
end StatMech.Universality
