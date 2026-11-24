module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part2
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


theorem innerEdge_injective (d n : ℕ) : Function.Injective (innerEdge d n) :=
  Sym2.map.injective (boxVertIncl_injective d n)


theorem edgeIncl_innerEdge (d n : ℕ) (e : Sym2 (boxVerts d n)) :
    edgeIncl d (n+1) (innerEdge d n e) = edgeIncl d n e := by
  unfold edgeIncl innerEdge
  rw [Sym2.map_map]
  rfl


end FK
end StatMech
