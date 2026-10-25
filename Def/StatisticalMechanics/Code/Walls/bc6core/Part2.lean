/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc6edgedichotomy
import Theorem.StatisticalMechanics.Code.Walls.bc6corridoraxisunique
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc6stepsameray
import Theorem.StatisticalMechanics.Code.Walls.bc6core.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc6_CorridorArmsDisjoint (N : ℕ) (j₁ j₂ j₃ : Fin d) (ω : ConfigSpace (Sym2 (Site d))) :
    Prop :=
  let G := bc3_corridorUnion j₁ j₂ j₃ N N N
  (bc6_ArmClosed N j₁ (N + 1) G ω ∧ bc6_ArmClosed N j₂ (N + 1) G ω ∧
    bc6_ArmClosed N j₃ (N + 1) G ω) ∧
  ((hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω ∧
    (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω)


end Walls
end StatMech
