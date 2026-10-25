/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def isingFiniteGraphBoundaryVertices
    {V : Type*} [Fintype V] (boundary : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter boundary

end
end StatMech.Universality
