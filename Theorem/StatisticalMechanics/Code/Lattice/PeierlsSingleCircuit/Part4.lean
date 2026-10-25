/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


theorem boundarySupport_spec {K : Set (Site 2)} (hK : K.Finite) :
    (faceBoundaryGraph K).support ⊆ (boundarySupport hK : Set (Site 2)) :=
  (exists_finset_support_faceBoundaryGraph K hK).choose_spec


theorem exists_single_dualCircuit_of_connected {K : Set (Site 2)} (hK : K.Finite)
    (hconn : FaceBoundaryConnected K (boundarySupport hK))
    {f₀ : Site 2} (hf₀ : f₀ ∈ (boundarySupport hK : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit (boundarySupport_spec hK) hconn hf₀


theorem faceBoundaryConnected_satisfiable_iff {K : Set (Site 2)} {T : Finset (Site 2)} :
    FaceBoundaryConnected K T ↔ ((faceBoundaryGraph K).induce (T : Set (Site 2))).Connected :=
  Iff.rfl


theorem triangle_connected : (completeGraph (Fin 3)).Connected := SimpleGraph.connected_top


theorem triangle_even_degree (v : Fin 3) : Even ((completeGraph (Fin 3)).degree v) := by
  rw [SimpleGraph.complete_graph_degree]
  decide


theorem triangle_eulerian :
    ∃ p : (completeGraph (Fin 3)).Walk 0 0,
      p.IsTrail ∧ (∀ e ∈ (completeGraph (Fin 3)).edgeFinset, e ∈ p.edges) ∧
        p.length = (completeGraph (Fin 3)).edgeFinset.card :=
  EulerianExistence.exists_closed_eulerian_length (completeGraph (Fin 3))
    triangle_connected triangle_even_degree 0


theorem triangle_edge_card : (completeGraph (Fin 3)).edgeFinset.card = 3 := by decide

end Lattice
end StatMech
