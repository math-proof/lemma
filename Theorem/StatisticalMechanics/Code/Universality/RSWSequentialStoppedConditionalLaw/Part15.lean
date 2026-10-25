/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_edgeProduct_exteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) [DecidableRel H.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.edgeProduct H p
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p
          (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
  classical
  let O := H.edgeFinset \
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  have hfactor : rlc_connectorExteriorEdgeFactor gamma gamma' H psi p =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    unfold rlc_connectorExteriorEdgeFactor
    apply Finset.prod_congr
    · ext e
      simp [O]
    · intro e he
      rfl
  have hsub : (rlc_connectorFiniteGraph gamma gamma').edgeFinset ⊆
      H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact hGH he
  have hedges : H.edgeFinset =
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset ∪ O := by
    exact (Finset.union_sdiff_of_subset hsub).symm
  have hdisj : Disjoint
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset O :=
    Finset.disjoint_sdiff
  have hinner :
      (∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
        if rlc_connectorExteriorFibreConfig gamma gamma' psi eta e
          then p else 1 - p) =
      ∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
        if FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta e
          then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heSet : e ∈
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      rwa [← SimpleGraph.mem_edgeFinset]
    have hfibre : rlc_connectorExteriorFibreConfig
        gamma gamma' psi eta e = eta ⟨e, heSet⟩ := by
      simp [rlc_connectorExteriorFibreConfig, heSet]
    have hactive := FK.extendActive_apply
      (rlc_connectorFiniteGraph gamma gamma') eta ⟨e, heSet⟩
    rw [hfibre, hactive]
  have houter :
      (∏ e ∈ O,
        if rlc_connectorExteriorFibreConfig gamma gamma' psi eta e
          then p else 1 - p) =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heNot : e ∉
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      have : e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeFinset :=
        (Finset.mem_sdiff.mp he).2
      simpa [SimpleGraph.mem_edgeFinset] using this
    have hfibre : rlc_connectorExteriorFibreConfig
        gamma gamma' psi eta e = psi e := by
      simp [rlc_connectorExteriorFibreConfig, heNot]
    rw [hfibre]
  unfold FK.edgeProduct
  rw [hedges, Finset.prod_union hdisj, hinner, houter, hfactor]
  exact mul_comm
    (∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
      if FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta e
        then p else 1 - p)
    (∏ e ∈ O, if psi e then p else 1 - p)


theorem rlc_bcWeight_exteriorFibre_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.bcWeight H B p q
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by
  rw [FK.bcWeight,
    rlc_edgeProduct_exteriorFibre gamma gamma' H hGH psi p eta,
    rlc_numClustersBC_exteriorFibre_eq_induced
      gamma gamma' H B hGH psi eta]
  rw [FK.activeBCWeight_const_eq_bcWeight]
  unfold FK.bcWeight
  ring

set_option maxHeartbeats 800000 in


theorem rlc_connectorExteriorFibre_inducedBcZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) :
    FK.inducedBcZ H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q := by
  unfold FK.inducedBcZ FK.activeBCZ
  let S := FK.condFibre
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
  let weight := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    FK.bcWeight H B p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((rlc_connectorExteriorFibreEquiv
        gamma gamma' psi) eta) :=
      (Equiv.sum_comp (rlc_connectorExteriorFibreEquiv gamma gamma' psi)
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact rlc_bcWeight_exteriorFibre_eq_induced
        gamma gamma' H B hGH psi p q eta
    _ = rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        ∑ eta, FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by rw [Finset.mul_sum]


theorem rlc_connectorExteriorFibre_condBcProb_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (fun _ => p) q eta := by
  unfold FK.condBcProb FK.activeBCProb
  rw [if_pos (rlc_connectorExteriorFibreConfig_agreesOff
    gamma gamma' psi eta)]
  rw [rlc_bcWeight_exteriorFibre_eq_induced
      gamma gamma' H B hGH psi p q eta,
    rlc_connectorExteriorFibre_inducedBcZ_eq
      gamma gamma' H B hGH psi p q]
  exact mul_div_mul_left _ _ (by
    unfold rlc_connectorExteriorEdgeFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    split
    · exact hp.ne'
    · exact (sub_pos.mpr hp1).ne')


end
end StatMech.Universality
