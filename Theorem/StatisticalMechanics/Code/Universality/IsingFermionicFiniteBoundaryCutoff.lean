/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteGraphBoundaryVertices_nonempty
    {V : Type*} [Fintype V] (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) :
    (isingFiniteGraphBoundaryVertices boundary).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hboundary
  exact ⟨x, by simp [isingFiniteGraphBoundaryVertices, hx]⟩


end
end StatMech.Universality
