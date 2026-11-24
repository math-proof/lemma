module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
public import Theorem.StatisticalMechanics.Code.FK.IvProperties
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Def.StatisticalMechanics.Code.FK.InducedBC.Part7
open scoped BigOperators
open SimpleGraph
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


@[simp] theorem isOutsideOnly_mk (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (v : boxVerts d (n+1)) :
    IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v) ↔ OutsideOnly d n ψ v :=
  Iff.rfl


end FK
end StatMech
