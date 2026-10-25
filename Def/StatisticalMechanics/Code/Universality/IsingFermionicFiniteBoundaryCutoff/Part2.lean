/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def isingFiniteGraphDistanceToBoundary
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) : Nat := by
  classical
  let B := isingFiniteGraphBoundaryVertices boundary
  have hB : B.Nonempty :=
    isingFiniteGraphBoundaryVertices_nonempty boundary hboundary
  exact (B.image (G.dist x)).min' (hB.image _)

end
end StatMech.Universality
