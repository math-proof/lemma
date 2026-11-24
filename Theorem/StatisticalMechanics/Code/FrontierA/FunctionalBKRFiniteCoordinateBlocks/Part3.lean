module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
public import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part3
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


theorem wholeBlocks_disjoint {K L : Set E} (hKL : Disjoint K L) :
    Disjoint (wholeBlocks (D := D) K) (wholeBlocks (D := D) L) := by
  rw [Set.disjoint_left]
  intro z hzK hzL
  exact Set.disjoint_left.1 hKL hzK hzL


end StatMech.FrontierA
