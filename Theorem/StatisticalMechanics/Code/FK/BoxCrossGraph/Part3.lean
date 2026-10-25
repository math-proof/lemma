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
import Instance.StatisticalMechanics.Code.FK.BoxCrossGraph
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem isInnerVert_iff_range (d n : ℕ) (v : boxVerts d (n+1)) :
    IsInnerVert d n v ↔ ∃ x, boxVertIncl d n x = v := by
  constructor
  · intro h
    exact ⟨⟨(v : Site d), h⟩, by apply Subtype.ext; rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.2


theorem isInnerVert_boxVertIncl (d n : ℕ) (x : boxVerts d n) :
    IsInnerVert d n (boxVertIncl d n x) := x.2


end FK
end StatMech
