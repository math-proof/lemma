module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part4
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


theorem crossExt_innerEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (e : Sym2 (boxVerts d n)) : crossExt d n ω (innerEdge d n e) = ω e := by
  unfold crossExt
  have hmem : innerEdge d n e ∈ Set.range (innerEdge d n) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact innerEdge_injective d n hmem.choose_spec


end FK
end StatMech
