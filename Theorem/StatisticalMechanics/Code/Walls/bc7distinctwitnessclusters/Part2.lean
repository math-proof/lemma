/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7distinctwitnessclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc4_core
import Def.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc7_distinctWitnessClusters (n : ℕ) : bc7_DistinctWitnessClusters d n := by
  intro ω hω
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
      x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩ :=
    bc4c_distinctWitnessClusters n ω hω
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
    x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃,
    bc7_cutCluster_ne ω hx₁' hx₂' hd12,
    bc7_cutCluster_ne ω hx₁' hx₃' hd13,
    bc7_cutCluster_ne ω hx₂' hx₃' hd23⟩

end Walls
end StatMech
