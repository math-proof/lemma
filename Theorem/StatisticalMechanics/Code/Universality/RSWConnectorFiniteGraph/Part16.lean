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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part22
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorPIMSExteriorTraceLocal gamma gamma' ↔
      rlc_connectorPIMSExteriorGraph gamma gamma' ≤
        rlc_connectorSeparateWiring gamma gamma' := by
  constructor
  · intro hlocal x y hxy
    rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj]
    rcases hlocal hxy with hright | hleft
    · left
      rw [Lattice.boundaryCliqueGraph_adj]
      exact ⟨hxy.ne, hright⟩
    · right
      rw [Lattice.boundaryCliqueGraph_adj]
      exact ⟨hxy.ne, hleft⟩
  · intro hle x y hxy
    have hsep := hle hxy
    rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
    rcases hsep with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact Or.inl hright.2
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact Or.inr hleft.2


theorem rlc_connectorPIMSExteriorTraceLocal_or_badEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorPIMSExteriorTraceLocal gamma gamma' ∨
      ∃ x y : RlcConnectorVertex n,
        (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y ∧
        ¬ ((rlc_connectorOnRight gamma x ∧
              rlc_connectorOnRight gamma y) ∨
            (rlc_connectorOnLeft gamma' x ∧
              rlc_connectorOnLeft gamma' y)) := by
  classical
  by_cases hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma'
  · exact Or.inl hlocal
  · right
    unfold RlcConnectorPIMSExteriorTraceLocal at hlocal
    push Not at hlocal
    obtain ⟨x, y, hxy, hright, hleft⟩ := hlocal
    refine ⟨x, y, hxy, ?_⟩
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact hright hx hy
    · exact hleft hx hy


theorem not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff {n : Int} :
    ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality n ↔
      ∃ (pair : RlcDiagonalPathPair n)
        (omega : ConfigSpace (Sym2 (Site 2)))
        (x y : RlcConnectorVertex n),
        omega ∈ rlc_extremalPairCandidate pair ∧
        (rlc_connectorPIMSExteriorGraph pair.1 pair.2).Adj x y ∧
        ¬ ((rlc_connectorOnRight pair.1 x ∧
              rlc_connectorOnRight pair.1 y) ∨
            (rlc_connectorOnLeft pair.2 x ∧
              rlc_connectorOnLeft pair.2 y)) := by
  classical
  constructor
  · intro hselection
    unfold RlcConnectorPIMSExtremalSelectionExteriorLocality at hselection
    push Not at hselection
    obtain ⟨pair, ⟨omega, hpair⟩, hlocal⟩ := hselection
    rcases rlc_connectorPIMSExteriorTraceLocal_or_badEdge pair.1 pair.2 with
      hgood | ⟨x, y, hxy, hbad⟩
    · exact (hlocal hgood).elim
    · exact ⟨pair, omega, x, y, hpair, hxy, hbad⟩
  · rintro ⟨pair, omega, x, y, hpair, hxy, hbad⟩ hselection
    exact hbad (hselection pair ⟨omega, hpair⟩ hxy)

end
end StatMech.Universality
