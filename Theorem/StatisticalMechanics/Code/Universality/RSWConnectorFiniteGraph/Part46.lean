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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part64
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterConfig_agreesOff_of_outerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (houter : rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) =
      rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerOuterVertex gamma gamma'))
      (rlc_connectorOuterDualConfig gamma gamma' tau)
      (rlc_connectorOuterDualConfig gamma gamma' sigma) := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
      have hfmem := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
      change (rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
      rcases hfmem with hfinite | htrace
      · let ef : (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hfinite⟩
        have heq : f.1 = ef.1 := hedge
        have hef : ef ∉ Set.range
            (rlc_connectorInnerSourceEdge gamma gamma') := by
          intro hmem
          obtain ⟨e, he⟩ := hmem
          apply haRange
          rw [← hrandom.choose_spec]
          apply (rlc_connectorOuterDualEdge_mem_innerRange_iff
            gamma gamma' f).2
          refine ⟨e, ?_⟩
          calc
            f.1 = ef.1 := heq
            _ = (rlc_connectorInnerSourceEdge gamma gamma' e).1 :=
              (congrArg Subtype.val he).symm
        have hcoord := congrFun houter ⟨ef, hef⟩
        simp only [rlc_connectorOuterActiveOfSource,
          FK.restrictActive] at hcoord
        have htau := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' tau ef
        have hsigma := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' sigma ef
        have htau' : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = tau s(x, y) := by simpa [ef] using htau
        have hsigma' : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = sigma s(x, y) := by simpa [ef] using hsigma
        have hforce : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = rlc_connectorForceTraceConfig gamma gamma' tau
              s(x, y) := hsigma'.trans (hcoord.symm.trans htau'.symm)
        exact congrArg Bool.not hforce
      · have hmem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        have htau : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        have hsigma : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        exact congrArg Bool.not (hsigma.trans htau.symm)
  · rfl


theorem rlc_connectorSplitSource_outProj_independent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta eta' : ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
  let tau := rlc_connectorSplitSourceConfig gamma gamma' eta xi
  let sigma := rlc_connectorSplitSourceConfig gamma gamma' eta' xi
  have hagree : FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerOuterVertex gamma gamma'))
      (rlc_connectorOuterDualConfig gamma gamma' tau)
      (rlc_connectorOuterDualConfig gamma gamma' sigma) :=
    rlc_connectorOuterConfig_agreesOff_of_outerActive
      gamma gamma' tau sigma (by
        funext e
        simp [tau, sigma, rlc_connectorSplitSourceConfig,
          rlc_connectorOuterActiveOfSource])
  unfold FK.AgreesOff at hagree
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerOuterVertex gamma gamma'))
  · rw [FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm

theorem rlc_connectorEmptyBoundary_eq_bot {V : Type*}
    [Fintype V] [DecidableEq V] :
    Lattice.boundaryCliqueGraph (fun _ : V => False) =
      (⊥ : SimpleGraph V) := by
  ext x y
  rw [Lattice.boundaryCliqueGraph_adj]
  simp

theorem rlc_connector_bcWeight_emptyBoundary_eq_bot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    FK.bcWeight G (Lattice.boundaryCliqueGraph (fun _ : V => False))
        p q omega =
      FK.bcWeight G ⊥ p q omega := by
  unfold FK.bcWeight FK.numClustersBC
  rw [rlc_connectorEmptyBoundary_eq_bot]


end
end StatMech.Universality
