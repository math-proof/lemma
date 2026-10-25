/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part2
open MeasureTheory


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


theorem hypercubicLattice_adj_signNormalize
    (mask x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingSignNormalize mask x) (isingSignNormalize mask y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingSignNormalize mask x a -
      isingSignNormalize mask y a).natAbs) = 1
  have hsum :
      (∑ a, (isingSignNormalize mask x a -
        isingSignNormalize mask y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : mask a < 0
    · simp only [isingSignNormalize, if_pos ha]
      rw [show -x a - -y a = -(x a - y a) by ring, Int.natAbs_neg]
    · simp [isingSignNormalize, ha]
  rw [hsum]

theorem mem_boxFinset_signNormalize_iff
    (mask : Site d) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔
      isingSignNormalize mask x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor <;> intro hx a
  · by_cases ha : mask a < 0
    · simpa [isingSignNormalize, ha] using hx a
    · simpa [isingSignNormalize, ha] using hx a
  · have h := hx a
    by_cases ha : mask a < 0
    · simpa [isingSignNormalize, ha] using h
    · simpa [isingSignNormalize, ha] using h

end StatMech.FrontierA
