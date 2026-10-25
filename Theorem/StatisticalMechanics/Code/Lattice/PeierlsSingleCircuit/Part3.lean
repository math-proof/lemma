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
import Def.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


theorem faceBoundaryGraph_single_dualCircuit {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (T : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges :=
  EulerianExistence.exists_closed_eulerian_of_finite_support (faceBoundaryGraph K) T hsupp hconn
    (degree_faceBoundaryGraph_even K) hf₀


end Lattice
end StatMech
