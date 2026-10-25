/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


@[simp] theorem boxVertIncl_val (d n : ℕ) (x : boxVerts d n) :
    ((boxVertIncl d n x : boxVerts d (n+1)) : Site d) = (x : Site d) := rfl

theorem boxVertIncl_injective (d n : ℕ) : Function.Injective (boxVertIncl d n) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (Subtype.val) h
  simpa [boxVertIncl] using this


theorem boxGraph_adj_boxVertIncl (d n : ℕ) (x y : boxVerts d n) :
    (boxGraph d (n+1)).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (boxGraph d n).Adj x y := by
  unfold boxGraph
  simp only [SimpleGraph.comap_adj, boxVertIncl_val]


theorem boxGraph_eq_comap (d n : ℕ) :
    boxGraph d n = (boxGraph d (n+1)).comap (boxVertIncl d n) := by
  ext x y
  rw [SimpleGraph.comap_adj, boxGraph_adj_boxVertIncl]


end FK
end StatMech
