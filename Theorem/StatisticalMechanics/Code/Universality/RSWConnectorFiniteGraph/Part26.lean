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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorForceFourTraceConfig_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorVertex n)}
    (he : e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau e = true := by
  simp [rlc_connectorForceFourTraceConfig, he]

@[simp] theorem rlc_connectorForceFourTraceConfig_reflected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorVertex n)}
    (he : e ∈
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset)
    (hnot : e ∉ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau e = false := by
  simp [rlc_connectorForceFourTraceConfig, he, hnot]

@[simp] theorem rlc_connectorForceFourTraceConfig_corridor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau s(x, y) =
      tau s(x, y) := by
  have hnotExposed : s(x, y) ∉
      (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
    intro hmem
    exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma' hxy
      ((SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hmem))
  have hnotReflected : s(x, y) ∉
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset := by
    intro hmem
    have href := (SimpleGraph.mem_edgeSet _).mp
      (SimpleGraph.mem_edgeFinset.mp hmem)
    rcases Finset.mem_union.mp href.2 with hright | hleft
    · unfold rlc_reflectedPathEdges at hright
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hright
      have hmapped : e.map rlc_flipX ∈
          rlc_connectorEdges gamma gamma' := by
        simpa [heq] using hxy.2
      have heConnector :=
        (rlc_connectorEdges_mem_map_flipX_iff gamma gamma' e).mpr hmapped
      exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma')) he heConnector
    · unfold rlc_reflectedPathEdges at hleft
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hleft
      have hmapped : e.map rlc_flipX ∈
          rlc_connectorEdges gamma gamma' := by
        simpa [heq] using hxy.2
      have heConnector :=
        (rlc_connectorEdges_mem_map_flipX_iff gamma gamma' e).mpr hmapped
      exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma')) he heConnector
  simp [rlc_connectorForceFourTraceConfig, hnotExposed, hnotReflected]


theorem rlc_openSub_fourTrace_force {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFourTracePlanarDomain gamma gamma').G
        (rlc_connectorForceFourTraceConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨(hfinite | htrace) | hreflected, hopen⟩
    · left
      refine ⟨hfinite, ?_⟩
      exact (rlc_connectorForceFourTraceConfig_corridor
        gamma gamma' tau hfinite).symm.trans hopen
    · exact Or.inr htrace
    · by_cases htrace :
          (rlc_connectorTraceWiring gamma gamma').Adj x y
      · exact Or.inr htrace
      · have hreflectedMem : s(x, y) ∈
            (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr hreflected)
        have htraceMem : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htrace ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        have hclosed := rlc_connectorForceFourTraceConfig_reflected
          gamma gamma' tau hreflectedMem htraceMem
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · rintro (⟨hfinite, hopen⟩ | htrace)
    · refine ⟨Or.inl (Or.inl hfinite), ?_⟩
      exact (rlc_connectorForceFourTraceConfig_corridor
        gamma gamma' tau hfinite).trans hopen
    · refine ⟨Or.inl (Or.inr htrace), ?_⟩
      apply rlc_connectorForceFourTraceConfig_exposed gamma gamma' tau
      exact SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet _).mpr htrace)


end
end StatMech.Universality
