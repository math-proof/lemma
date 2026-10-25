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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part44
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorOuterDualConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualConfig gamma gamma' tau
        (rlc_connectorOuterDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_connectorOuterDualEdge_injective gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim


theorem rlc_connectorOuterDualConfig_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorOuterDualVertex gamma gamma')}
    (he : e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet) :
    rlc_connectorOuterDualConfig gamma gamma' tau e = true := by
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i hrandom
    obtain ⟨f, rfl⟩ := hrandom
    exact (rlc_connectorOuterDualEdge_not_mem_spoke
      gamma gamma' f he).elim
  · simp [he]


theorem rlc_connectorOuterFaceProjection_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorOuterDualEdge gamma gamma' f).map
        (rlc_connectorOuterFaceProjection gamma gamma') =
      Ising.kwg_dualEnds
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_connectorOuterTargetVertex,
      rlc_connectorOuterFaceProjection,
      rlc_connectorReflectedDualEdge, Ising.kwg_dualEnds,
      Sym2.map_map] using hmapped
  · simp [rlc_connectorOuterPort,
      rlc_connectorOuterFaceProjection, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace]


end
end StatMech.Universality
