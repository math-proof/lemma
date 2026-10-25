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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorTraceFibreConfig_agreesOff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma')
      (rlc_connectorTraceFibreReference gamma gamma')
      (rlc_connectorTraceFibreConfig gamma gamma' eta) := by
  intro e he
  by_cases htrace : e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset
  · simp [rlc_connectorTraceFibreReference,
      rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig, htrace]
  · have hnotG : e ∉
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      intro heG
      apply he
      exact SimpleGraph.mem_edgeFinset.mpr heG
    simp [rlc_connectorTraceFibreReference,
      rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
      FK.extendActive, htrace, hnotG]


@[simp] theorem rlc_connectorTraceFibreConfig_restrictActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorTraceFibreConfig gamma gamma' eta) = eta := by
  funext e
  unfold FK.restrictActive rlc_connectorTraceFibreConfig
  rw [rlc_connectorForceTraceConfig_finiteEdge]
  exact FK.extendActive_apply _ _ _


theorem rlc_connectorTraceFibreConfig_restrictActive_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hrho : FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma')
      (rlc_connectorTraceFibreReference gamma gamma') rho) :
    rlc_connectorTraceFibreConfig gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) =
      rho := by
  funext e
  by_cases heG : e ∈
      (rlc_connectorFiniteGraph gamma gamma').edgeSet
  · have hnotTrace : e ∉
        (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
      intro htrace
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hG : (rlc_connectorFiniteGraph gamma gamma').Adj x y :=
            (SimpleGraph.mem_edgeSet _).mp heG
          have hT : (rlc_connectorTraceWiring gamma gamma').Adj x y :=
            (SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp htrace)
          exact rlc_connectorFiniteGraph_adj_not_traceWiring
            gamma gamma' hG hT
    simp [rlc_connectorTraceFibreConfig,
      rlc_connectorForceTraceConfig, hnotTrace, FK.extendActive,
      FK.restrictActive, heG]
  · have heFin : e ∉ rlc_connectorTraceFibreInside gamma gamma' := by
      simpa [rlc_connectorTraceFibreInside,
        SimpleGraph.mem_edgeFinset] using heG
    rw [hrho e heFin]
    by_cases htrace : e ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
    · simp [rlc_connectorTraceFibreReference,
        rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
        htrace]
    · simp [rlc_connectorTraceFibreReference,
        rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
        FK.extendActive, htrace, heG]


end
end StatMech.Universality
