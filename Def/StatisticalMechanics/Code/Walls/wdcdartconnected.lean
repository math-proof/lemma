/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


def wdc_boundaryLayer (K : Set (Site 2)) : Set (Site 2) :=
  {v | v ∉ K ∧ ∃ s : Site 2, (hypercubicLattice 2).Adj s v ∧ s ∈ K}


end Wots
end StatMech
