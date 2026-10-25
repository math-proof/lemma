/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem edgeSubsetFibreConfig_agreesOff (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    AgreesOff K.edgeFinset psi (edgeSubsetFibreConfig K psi eta) := by
  intro e he
  have hnot : e ∉ K.edgeSet := by
    intro hmem
    exact he (SimpleGraph.mem_edgeFinset.mpr hmem)
  simp [edgeSubsetFibreConfig, hnot]

@[simp] theorem edgeSubsetFibreConfig_restrictActive (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    restrictActive K (edgeSubsetFibreConfig K psi eta) = eta := by
  funext e
  simp [restrictActive, edgeSubsetFibreConfig, e.2]

theorem edgeSubsetFibreConfig_restrictActive_eq (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi rho : ConfigSpace (Sym2 V))
    (hrho : AgreesOff K.edgeFinset psi rho) :
    edgeSubsetFibreConfig K psi (restrictActive K rho) = rho := by
  funext e
  by_cases he : e ∈ K.edgeSet
  · simp [edgeSubsetFibreConfig, restrictActive, he]
  · rw [edgeSubsetFibreConfig, dif_neg he]
    exact (hrho e (by
      simpa [SimpleGraph.mem_edgeFinset] using he)).symm


end
end StatMech.FK
