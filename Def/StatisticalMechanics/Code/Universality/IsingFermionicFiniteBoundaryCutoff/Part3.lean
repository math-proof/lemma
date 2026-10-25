/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def isingFiniteGraphBoundaryTentCutoff
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (x : V) : Real :=
  min 1 ((isingFiniteGraphDistanceToBoundary G boundary hboundary x : Real) /
    (r : Real))

end
end StatMech.Universality
