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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part68
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorSplitOuterEventMass_eq_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorSplitOuterEventMass gamma gamma' p q A =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        rlc_connectorFibreWeight gamma gamma' p q xi *
          FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
            (rlc_connectorInnerInducedWiring gamma gamma'
              (rlc_connectorOuterStateOfSource gamma gamma' xi))
            (fun _ => p) q A := by
  unfold rlc_connectorSplitOuterEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xi _
  rw [show (∑ eta,
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
          (rlc_connectorInnerOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorOuterStateOfSource gamma gamma' xi) p q *
        FK.activeBCNumer (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerInducedWiring gamma gamma'
            (rlc_connectorOuterStateOfSource gamma gamma' xi))
          (fun _ => p) q (A.indicator fun _ => (1 : Real)) by
    unfold FK.activeBCNumer
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    rw [rlc_connectorSplitSource_outerWeight]
    ring]
  unfold rlc_connectorFibreWeight FK.activeBCProbOf
  rw [FK.activeBCMean_eq_div]
  have hZi := (FK.activeBCZ_pos
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerInducedWiring gamma gamma'
      (rlc_connectorOuterStateOfSource gamma gamma' xi))
    (fun _ => hp) (fun _ => hp1) hq).ne'
  field_simp


theorem rlc_connectorForceTraceConfig_activeCanonical {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorForceTraceConfig gamma gamma' tau f.1 =
      rlc_connectorForceTraceConfig gamma gamma'
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau))
        f.1 := by
  unfold rlc_connectorForceTraceConfig
  split
  · rfl
  · rename_i hnot
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
      have hf := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hf
      change (rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hf
      rcases hf with hfinite | htrace
      · let e : (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hfinite⟩
        exact (FK.extendActive_apply
          (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)
          e).symm
      · apply (hnot ?_).elim
        rw [hedge]
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.mem_edgeSet _).mpr htrace)


theorem rlc_connectorOuterDualConfig_activeCanonical {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorOuterDualConfig gamma gamma' tau =
      rlc_connectorOuterDualConfig gamma gamma'
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)) := by
  funext a
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i h
    rw [rlc_connectorForceTraceConfig_activeCanonical
      gamma gamma' tau h.choose]
  · rfl


theorem rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorOuterRestrictedZ gamma gamma' p q =
      2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
        rlc_connectorFibreMixtureZ gamma gamma' p q := by
  unfold rlc_connectorOuterRestrictedZ
  rw [← Equiv.sum_comp
    (FK.activeSplitEquiv (rlc_connectorFiniteGraph gamma gamma')).symm,
    Fintype.sum_prod_type]
  have hinactive : forall eta : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (RlcConnectorVertex n) //
          e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet},
        FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma'
            ((FK.activeSplitEquiv
              (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)))) =
        2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (FK.extendActive
                (rlc_connectorFiniteGraph gamma gamma') eta)) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      have hconfig : rlc_connectorOuterDualConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorOuterDualConfig gamma gamma'
            (FK.extendActive
              (rlc_connectorFiniteGraph gamma gamma') eta) := by
        rw [rlc_connectorOuterDualConfig_activeCanonical,
          FK.restrictActive_activeSplitEquiv_symm]
      exact congrArg
        (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q)
        hconfig),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      FK.card_inactive_config]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => hinactive eta),
    ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp
    (rlc_connectorSourceActiveEquiv gamma gamma').symm,
    Fintype.sum_prod_type, Finset.sum_comm,
    rlc_connectorFibreMixtureZ_eq_sum_outerWeight]
  rfl


end
end StatMech.Universality
