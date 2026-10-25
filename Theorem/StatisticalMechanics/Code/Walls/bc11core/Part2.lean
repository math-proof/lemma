/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc9core
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters.Part2
import Def.StatisticalMechanics.Code.Walls.bc11core.Part2
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc11_boxOriginReach_of_attachData_and_openIncidence (n : ℕ)
    (hattach : tex_BoxAttachData d n) (hinc : bc11_BoxOriginOpenIncidence d n) :
    bc9_BoxOriginReach d n := by
  intro ω hω
  
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
      _x₁', _x₂', _x₃', _, _, _, _, _, _, _, _, _⟩ :=
    bc7_distinctWitnessClusters n ω hω
  
  have hAttach : tex_AttachData ω x₁ x₂ x₃ :=
    hattach ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
  
  exact bc11_boxReach_of_attachData ω x₁ x₂ x₃ hd12 hd13 hd23 hAttach
    (fun a₁ a₂ a₃ W hW0 hadj1 hadj2 hadj3 ha1 ha2 ha3 =>
      hinc ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23
        a₁ a₂ a₃ W hW0 hadj1 hadj2 hadj3 ha1 ha2 ha3)


theorem bc11_originRewiring_of_attachData_and_openIncidence (n : ℕ)
    (hattach : tex_BoxAttachData d n) (hinc : bc11_BoxOriginOpenIncidence d n) :
    bc8_OriginRewiring d n :=
  bc9_originRewiring_of_boxOriginReach n
    (bc11_boxOriginReach_of_attachData_and_openIncidence n hattach hinc)


end Walls
end StatMech
