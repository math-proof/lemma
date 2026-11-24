module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part11
open scoped BigOperators
open SimpleGraph
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice


theorem mem_innerEdgeFinset (d n : ℕ) (e : Sym2 (boxVerts d (n+1))) :
    e ∈ innerEdgeFinset d n ↔ e ∈ Set.range (innerEdge d n) := by
  simp only [innerEdgeFinset, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]


end FK
end StatMech
