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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part33
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorInnerCollared_outerWeight_factorization {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma')))
    (p q : Real) :
    FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_psiExt
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          psi omega) =
      FK.bcWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi)
          p q omega *
        FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False) psi p q := by
  simpa [rlc_connectorInnerCollaredInducedWiring] using
    (FK.ocd_bcWeight_psiExt
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
      (rlc_connectorInnerCollaredOuter_adjMatch gamma gamma')
      (p := p) (q := q) psi omega)


theorem rlc_connectorInnerCollared_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :
    FK.condBcProb (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')) psi
        (FK.ocd_psiExt
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          psi omega) =
      FK.bcProb (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi)
        p q omega := by
  simpa [rlc_connectorInnerCollaredInducedWiring] using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
      (rlc_connectorInnerCollaredOuter_adjMatch gamma gamma')
      hp hp1 hq psi omega)


theorem rlc_connectorCollaredOuterDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorCollaredOuterDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      e.1.map (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
  let v := rlc_connectorInnerEdgeToVariable gamma gamma' e
  let f := rlc_connectorInnerAugmentedEdge gamma gamma' e
  have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
      v.1.map Subtype.val := by
    exact rlc_connectorReflectedDualEdge_innerAugmented gamma gamma' e
  have hret : RlcConnectorRetainedDualEdge gamma gamma' f :=
    ⟨v, hreflected.symm⟩
  unfold rlc_connectorCollaredOuterDualEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = v.1 := by
    apply rlc_sym2Map_subtypeVal_injective
    exact hret.choose_spec.trans hreflected
  rw [hedge]
  simp [v, rlc_connectorInnerEdgeToVariable,
    rlc_connectorInnerCollaredOuterVertex,
    rlc_connectorCollaredOuterTargetVertex, Sym2.map_map]

@[simp] theorem rlc_connectorCollaredOuterDualConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorCollaredOuterDualConfig gamma gamma' tau
        (rlc_connectorCollaredOuterDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
  unfold rlc_connectorCollaredOuterDualConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_connectorCollaredOuterDualEdge_injective
        gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim


theorem rlc_connectorCollaredOuterConfig_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)) e =
      rlc_connectorInnerActiveOfSource gamma gamma'
        (FK.restrictActive
          (rlc_connectorFiniteGraph gamma gamma') tau) e := by
  unfold FK.restrictActive FK.ocd_innerRestrict
  change rlc_connectorCollaredOuterDualConfig gamma gamma' tau
      (e.1.map
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')) = _
  rw [← rlc_connectorCollaredOuterDualEdge_innerAugmented
      gamma gamma' e,
    rlc_connectorCollaredOuterDualConfig_randomEdge]
  rw [show (rlc_connectorInnerAugmentedEdge gamma gamma' e).1 =
      (rlc_connectorInnerSourceEdge gamma gamma' e).1 from rfl,
    rlc_connectorForceTraceConfig_finiteEdge]
  rfl


theorem rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (he : f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1) :
    rlc_connectorCollaredOuterDualEdge gamma gamma' f ∈
      Set.range (FK.ocd_innerEdge
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')) := by
  have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e := by
    apply Subtype.ext
    exact he
  rw [hf, rlc_connectorCollaredOuterDualEdge_innerAugmented]
  exact ⟨e.1, rfl⟩


theorem rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (houter : rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) =
      rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
      (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)
      (rlc_connectorCollaredOuterDualConfig gamma gamma' sigma) := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerCollaredOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_connectorCollaredOuterDualConfig
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
          apply rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source
            gamma gamma' f e
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

theorem rlc_connectorCollaredSplitSource_outProj_independent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta eta' : ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.ocd_outProj
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
  let tau := rlc_connectorSplitSourceConfig gamma gamma' eta xi
  let sigma := rlc_connectorSplitSourceConfig gamma gamma' eta' xi
  have hagree : FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
      (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)
      (rlc_connectorCollaredOuterDualConfig gamma gamma' sigma) :=
    rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive
      gamma gamma' tau sigma (by
        funext e
        simp [tau, sigma, rlc_connectorSplitSourceConfig,
          rlc_connectorOuterActiveOfSource])
  unfold FK.AgreesOff at hagree
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
  · rw [FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma') _ ha]
  · rw [FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm

end
end StatMech.Universality
