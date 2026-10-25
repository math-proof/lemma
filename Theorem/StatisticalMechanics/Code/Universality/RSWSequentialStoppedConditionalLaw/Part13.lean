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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_openSub_exteriorFibre_sup_frozen {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.openSub H (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) ⊔ B =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma')
          (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) ⊔
        rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hH, hopen⟩ | hB)
    · by_cases hG : (rlc_connectorFiniteGraph gamma gamma').Adj x y
      · left
        refine ⟨hG, ?_⟩
        have he : s(x, y) ∈
            (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hG
        rw [FK.extendActive_apply
          (rlc_connectorFiniteGraph gamma gamma') eta ⟨s(x, y), he⟩]
        simpa [rlc_connectorExteriorFibreConfig, he] using hopen
      · right
        exact Or.inl ⟨hH, hG, by
          simpa [rlc_connectorExteriorFibreConfig,
            show s(x, y) ∉
              (rlc_connectorFiniteGraph gamma gamma').edgeSet by
                rwa [SimpleGraph.mem_edgeSet]] using hopen⟩
    · exact Or.inr (Or.inr hB)
  · rintro (⟨hG, hopen⟩ | (hExt | hB))
    · left
      refine ⟨hGH hG, ?_⟩
      have he : s(x, y) ∈
          (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hG
      rw [rlc_connectorExteriorFibreConfig, dif_pos he]
      rw [FK.extendActive_apply
        (rlc_connectorFiniteGraph gamma gamma') eta ⟨s(x, y), he⟩] at hopen
      exact hopen
    · left
      refine ⟨hExt.1, ?_⟩
      have he : s(x, y) ∉
          (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
        exact hExt.2.1
      simpa [rlc_connectorExteriorFibreConfig, he] using hExt.2.2
    · exact Or.inr hB

theorem rlc_reachable_of_adj_reachable
    {V : Type*} {A K : SimpleGraph V}
    (hstep : ∀ {x y}, A.Adj x y → K.Reachable x y)
    {x y : V} (hxy : A.Reachable x y) : K.Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact .refl _
  | cons huv w ih => exact (hstep huv).trans ih


theorem rlc_sup_frozen_reachable_iff_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (A : SimpleGraph (RlcConnectorVertex n)) (x y : RlcConnectorVertex n) :
    (A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Reachable x y ↔
      (A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi).Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hA | hE
    · exact Or.inl hA
    · exact Or.inr ⟨hE.ne, hE.reachable⟩
  · intro hxy
    apply rlc_reachable_of_adj_reachable (A :=
      A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi) ?_ hxy
    intro u v huv
    rcases huv with hA | hC
    · exact (show (A ⊔
        rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Adj u v
        from Or.inl hA).reachable
    · exact hC.2.mono le_sup_right


end
end StatMech.Universality
