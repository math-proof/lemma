/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc63coarseforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc63_CoarseArmEmbedding (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  bc61_CoarseForestLeafCount ω L R


end StatMech.Walls
