/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.FK.InducedBC.Part2
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem outsideGraph_adj (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (x y : boxVerts d (n+1)) :
    (outsideGraph d n ψ).Adj x y
      ↔ ((boxGraph d (n+1)).Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (innerEdge d n))
        ∨ (x ≠ y ∧ boxBoundary d (n+1) x ∧ boxBoundary d (n+1) y) := by
  rw [outsideGraph, SimpleGraph.sup_adj, StatMech.Lattice.boundaryCliqueGraph_adj]
  exact Iff.rfl


end FK
end StatMech
