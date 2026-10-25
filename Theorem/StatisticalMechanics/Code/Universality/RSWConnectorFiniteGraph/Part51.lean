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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part69
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    (∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real)) tau *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma' tau)) =
      2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
        (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
          ∑ eta : ConfigSpace
              (rlc_connectorInnerGraph gamma gamma').edgeSet,
            A.indicator (fun _ => (1 : Real)) eta *
              FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
                (rlc_connectorOuterDualConfig gamma gamma'
                  (rlc_connectorSplitSourceConfig
                    gamma gamma' eta xi))) := by
  rw [← Equiv.sum_comp
    (FK.activeSplitEquiv (rlc_connectorFiniteGraph gamma gamma')).symm,
    Fintype.sum_prod_type]
  have hinactive : forall eta : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (RlcConnectorVertex n) //
          e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet},
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real))
            ((FK.activeSplitEquiv
              (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              ((FK.activeSplitEquiv
                (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)))) =
        2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
          (A.indicator (fun _ => (1 : Real))
              (rlc_connectorInnerActiveOfSource gamma gamma' eta) *
            FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
              (rlc_connectorOuterDualConfig gamma gamma'
                (FK.extendActive
                  (rlc_connectorFiniteGraph gamma gamma') eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      have hactive : rlc_connectorReducedStateOfConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorInnerActiveOfSource gamma gamma' eta := by
        simp only [rlc_connectorReducedStateOfConfig,
          FK.restrictActive_activeSplitEquiv_symm]
      have hconfig : rlc_connectorOuterDualConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorOuterDualConfig gamma gamma'
            (FK.extendActive
              (rlc_connectorFiniteGraph gamma gamma') eta) := by
        rw [rlc_connectorOuterDualConfig_activeCanonical,
          FK.restrictActive_activeSplitEquiv_symm]
      have hindicator :
          (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
          (fun _ => (1 : Real))
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          A.indicator (fun _ => (1 : Real))
            (rlc_connectorInnerActiveOfSource gamma gamma' eta) := by
        calc
          _ = A.indicator (fun _ => (1 : Real))
              (rlc_connectorReducedStateOfConfig gamma gamma'
                ((FK.activeSplitEquiv
                  (rlc_connectorFiniteGraph gamma gamma')).symm
                    (eta, xi))) := by
            simpa only [Function.comp_apply] using
              (Set.indicator_comp_right
                (rlc_connectorReducedStateOfConfig gamma gamma')
                (s := A) (g := fun _ => (1 : Real)))
          _ = _ := by rw [hactive]
      exact congrArg₂ (fun a b : Real => a * b) hindicator
        (congrArg
          (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q)
          hconfig)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      FK.card_inactive_config]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => hinactive eta),
    ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp
    (rlc_connectorSourceActiveEquiv gamma gamma').symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi _
  apply Finset.sum_congr rfl
  intro eta _
  have hpair := (rlc_connectorSourceActiveEquiv gamma gamma').right_inv
    (eta, xi)
  have hinner := congrArg Prod.fst hpair
  rw [show rlc_connectorInnerActiveOfSource gamma gamma'
      ((rlc_connectorSourceActiveEquiv gamma gamma').symm (eta, xi)) =
        eta by exact hinner]
  rfl


theorem rlc_connectorForcedDualReducedEventMass_eq_split {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) =
      rlc_connectorSplitOuterEventMass gamma gamma' p q A := by
  unfold rlc_connectorForcedDualEventMass
  simp_rw [← rlc_connectorOuterRestrictedProb_eq_forcedDualProb
    gamma gamma' _ hp]
  unfold rlc_connectorOuterRestrictedProb
  rw [show (∑ x,
      (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
          (fun _ => (1 : Real)) x *
        (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma' x) /
            rlc_connectorOuterRestrictedZ gamma gamma' p q)) =
      ∑ x,
        ((rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real)) x *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma' x)) /
          rlc_connectorOuterRestrictedZ gamma gamma' p q by
    apply Finset.sum_congr rfl
    intro x _
    ring,
    ← Finset.sum_div,
    rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer,
    rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture]
  unfold rlc_connectorSplitOuterEventMass
  have htwo : (2 : Real) ^
      FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') ≠ 0 := by
    positivity
  exact mul_div_mul_left _ _ htwo


end
end StatMech.Universality
