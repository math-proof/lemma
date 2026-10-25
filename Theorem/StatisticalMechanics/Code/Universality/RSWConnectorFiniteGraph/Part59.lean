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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part80
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredSplitSource_outProj_eq_state {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      rlc_connectorCollaredOuterStateOfSource gamma gamma' xi := by
  exact rlc_connectorCollaredSplitSource_outProj_independent
    gamma gamma' eta (fun _ => false) xi

theorem rlc_connectorCollaredOuterState_reconstruct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_psiExt
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      rlc_connectorCollaredOuterDualConfig gamma gamma'
        (rlc_connectorSplitSourceConfig gamma gamma' eta xi) := by
  let rho := rlc_connectorCollaredOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  have hstate : rlc_connectorCollaredOuterStateOfSource gamma gamma' xi =
      FK.ocd_outProj
        (rlc_connectorInnerCollaredOuterVertex gamma gamma') rho :=
    (rlc_connectorCollaredSplitSource_outProj_eq_state
      gamma gamma' eta xi).symm
  rw [hstate]
  apply FK.ocd_psiExt_innerRestrict_of_agreesOff
    (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
  intro a ha
  rw [FK.ocd_mem_innerEdgeFinset] at ha
  exact (FK.ocd_outProj_eq_of_not_range rho ha).symm

theorem rlc_connectorCollaredSplitSource_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      eta := by
  funext e
  rw [rlc_connectorCollaredOuterConfig_innerActive]
  rw [show FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSplitSourceConfig gamma gamma' eta xi) =
        rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) by
    unfold rlc_connectorSplitSourceConfig
    exact FK.restrictActive_extendActive _ _]
  have h := congrArg Prod.fst
    ((rlc_connectorSourceActiveEquiv gamma gamma').right_inv (eta, xi))
  exact congrFun h e


theorem rlc_connectorCollaredSplitSource_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (p q : Real) :
    FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.activeBCWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma'
            (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
          (fun _ => p) q eta *
        FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
          p q := by
  let rho := rlc_connectorCollaredOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  let psi := rlc_connectorCollaredOuterStateOfSource gamma gamma' xi
  let omega := FK.ocd_innerRestrict
    (rlc_connectorInnerCollaredOuterVertex gamma gamma') rho
  have hfactor := rlc_connectorInnerCollared_outerWeight_factorization
    gamma gamma' psi omega p q
  have hreconstruct := rlc_connectorCollaredOuterState_reconstruct
    gamma gamma' eta xi
  change FK.ocd_psiExt
    (rlc_connectorInnerCollaredOuterVertex gamma gamma')
    psi omega = rho at hreconstruct
  rw [hreconstruct] at hfactor
  rw [rlc_connector_bcWeight_emptyBoundary_eq_bot] at hfactor
  rw [hfactor]
  congr 1
  unfold FK.activeBCWeight
  apply FK.bcWeight_eq_of_edges
  intro e he
  have heSet : e ∈ (rlc_connectorInnerGraph gamma gamma').edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  let a : (rlc_connectorInnerGraph gamma gamma').edgeSet := ⟨e, heSet⟩
  calc
    omega e = FK.restrictActive
        (rlc_connectorInnerGraph gamma gamma') omega a := rfl
    _ = eta a := congrFun
      (rlc_connectorCollaredSplitSource_innerActive
        gamma gamma' eta xi) a
    _ = FK.extendActive (rlc_connectorInnerGraph gamma gamma') eta e :=
      (FK.extendActive_apply
        (rlc_connectorInnerGraph gamma gamma') eta a).symm

end
end StatMech.Universality
