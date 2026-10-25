/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Sharpness.IsingExponentialPlus
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising (spin plusState spin_eq_pm spin_sq boxFinset mem_boxFinset)

open Lattice Percolation ConfigSpace

variable {d : ℕ}


theorem isingSimonRadius_pos (T : Finset (Site d)) :
    0 < isingSimonRadius d T := by
  unfold isingSimonRadius
  omega

theorem cut_lt_isingSimonRadius (T : Finset (Site d)) {x : Site d}
    (hx : x ∈ T) : l1dist d (origin d) x < isingSimonRadius d T := by
  unfold isingSimonRadius
  have h := Finset.le_sup (f := fun x ↦ l1dist d (origin d) x) hx
  exact lt_of_le_of_lt (h.trans (Nat.le_max_left _ _))
    (Nat.lt_succ_self _)

theorem boundary_lt_isingSimonRadius (T : Finset (Site d))
    {e : Site d × Site d} (he : e ∈ boundaryEdges d T) :
    l1dist d (origin d) e.2 < isingSimonRadius d T := by
  unfold isingSimonRadius
  have h := Finset.le_sup
    (f := fun e ↦ l1dist d (origin d) e.2) he
  exact lt_of_le_of_lt (h.trans (Nat.le_max_right _ _))
    (Nat.lt_succ_self _)


end Sharpness
end StatMech
