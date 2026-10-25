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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part63
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorOuterDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      e.1.map (rlc_connectorInnerOuterVertex gamma gamma') := by
  let v := rlc_connectorInnerEdgeToVariable gamma gamma' e
  let f := rlc_connectorInnerAugmentedEdge gamma gamma' e
  have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
      v.1.map Subtype.val := by
    apply rlc_pimsEdgeEquiv.injective
    rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
    change (rlc_connectorInnerSourceEdge gamma gamma' e).1.map
      Subtype.val = rlc_pimsEdgeEquiv (v.1.map Subtype.val)
    exact rlc_connectorInnerSourceEdge_map gamma gamma' e
  have hret : RlcConnectorRetainedDualEdge gamma gamma' f :=
    ⟨v, hreflected.symm⟩
  unfold rlc_connectorOuterDualEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = v.1 := by
    apply rlc_sym2Map_subtypeVal_injective
    exact hret.choose_spec.trans hreflected
  rw [hedge]
  simp [v, rlc_connectorInnerEdgeToVariable,
    rlc_connectorInnerOuterVertex, Sym2.map_map]

theorem rlc_connectorReflectedDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorReflectedDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      (rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
        Subtype.val := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
  exact rlc_connectorInnerSourceEdge_map gamma gamma' e


theorem rlc_connectorOuterDualEdge_mem_innerRange_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
        Set.range (FK.ocd_innerEdge
          (rlc_connectorInnerOuterVertex gamma gamma')) ↔
      ∃ e : (rlc_connectorInnerGraph gamma gamma').edgeSet,
        f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1 := by
  constructor
  · rintro ⟨a, ha⟩
    induction a using Sym2.inductionOn with
    | _ x y =>
      have ha' : rlc_connectorOuterDualEdge gamma gamma' f =
          s(rlc_connectorInnerOuterVertex gamma gamma' x,
            rlc_connectorInnerOuterVertex gamma gamma' y) := by
        simpa [FK.ocd_innerEdge, Sym2.map_mk] using ha.symm
      have houter : (rlc_connectorOuterDualGraph gamma gamma').Adj
          (rlc_connectorInnerOuterVertex gamma gamma' x)
          (rlc_connectorInnerOuterVertex gamma gamma' y) := by
        rw [rlc_connectorOuterDualGraph, SimpleGraph.sup_adj]
        left
        refine ⟨?_, f, ha'⟩
        intro hxy
        have : x = y :=
          rlc_connectorInnerOuterVertex_injective gamma gamma' hxy
        subst y
        exact rlc_connectorOuterDualEdge_ne_diag gamma gamma' f _ ha'
      have hinner : (rlc_connectorInnerGraph gamma gamma').Adj x y :=
        (rlc_connectorInnerOuter_adjMatch gamma gamma' x y).mpr houter
      let e : (rlc_connectorInnerGraph gamma gamma').edgeSet :=
        ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hinner⟩
      have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
          (rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
            Subtype.val := by
        unfold rlc_connectorOuterDualEdge at ha'
        split at ha'
        · rename_i hret
          have hedge : hret.choose.1 =
              (rlc_connectorInnerEdgeToVariable gamma gamma' e).1 := by
            apply Sym2.map.injective
              (rlc_connectorOuterTargetVertex_injective gamma gamma')
            simpa [e, rlc_connectorInnerEdgeToVariable,
              rlc_connectorInnerOuterVertex, Sym2.map_map] using ha'
          exact hret.choose_spec.symm.trans <| by rw [hedge]
        · rw [Sym2.eq_iff] at ha'
          simp [rlc_connectorInnerOuterVertex,
            rlc_connectorOuterTargetVertex,
            rlc_connectorOuterPort] at ha'
      have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e :=
        rlc_connectorReflectedDualEdge_injective gamma gamma'
          (hreflected.trans
            (rlc_connectorReflectedDualEdge_innerAugmented
              gamma gamma' e).symm)
      exact ⟨e, congrArg Subtype.val hf⟩
  · rintro ⟨e, he⟩
    have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e := by
      apply Subtype.ext
      exact he
    rw [hf, rlc_connectorOuterDualEdge_innerAugmented]
    exact ⟨e.1, rfl⟩


theorem rlc_connectorOuterConfig_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerOuterVertex gamma gamma')
          (rlc_connectorOuterDualConfig gamma gamma' tau)) e =
      rlc_connectorInnerActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) e := by
  unfold FK.restrictActive FK.ocd_innerRestrict
  change rlc_connectorOuterDualConfig gamma gamma' tau
      (e.1.map (rlc_connectorInnerOuterVertex gamma gamma')) = _
  rw [← rlc_connectorOuterDualEdge_innerAugmented gamma gamma' e,
    rlc_connectorOuterDualConfig_randomEdge]
  rw [show (rlc_connectorInnerAugmentedEdge gamma gamma' e).1 =
      (rlc_connectorInnerSourceEdge gamma gamma' e).1 from rfl,
    rlc_connectorForceTraceConfig_finiteEdge]
  rfl


end
end StatMech.Universality
