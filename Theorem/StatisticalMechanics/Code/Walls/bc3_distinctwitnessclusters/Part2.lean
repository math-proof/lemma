/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Def.StatisticalMechanics.Code.Walls.bc3_distinctwitnessclusters
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_arm_cutInfinite_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (hres : bc3_OriginCutLeavesInfinite ω) (x : Site d) (hinf : (cluster d ω x).Infinite) :
    ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite := by
  by_cases h0 : (0 : Site d) ∈ cluster d ω x
  · exact hres x hinf h0
  · exact ⟨x, self_mem_cluster ω x, bc3_cutClusterInfinite_of_originNotMem ω x hinf h0⟩


theorem bc3_armEscapes_of_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) (x' : Site d)
    (hinf : (cluster d (removeSite 0 ω) x').Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x' y ∧
      (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 :=
  bc2_cutUnbounded ω x' hinf n


end Walls
end StatMech
