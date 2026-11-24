module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Instance.StatisticalMechanics.Code.FK.BoxCrossGraph.Part2
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


theorem innerBdry_boxVertIncl (d n : ℕ) (x : boxVerts d n) :
    innerBdry d n (boxVertIncl d n x) ↔ boxBoundary d n x := by
  unfold innerBdry boxBoundary
  simp only [boxVertIncl_val, isInnerVert_boxVertIncl, true_and]


theorem innerBdry_isInnerVert (d n : ℕ) {v : boxVerts d (n+1)} (h : innerBdry d n v) :
    IsInnerVert d n v := h.1


end FK
end StatMech
