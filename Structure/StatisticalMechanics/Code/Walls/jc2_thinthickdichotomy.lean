/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc2_ThinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  

  dichotomy : 1 ≤ len →
    (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨
      (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len))
  

  len_zero_split : len = 0 → ∀ v ∈ K, (hypercubicLattice 2).Adj v c →
    v = jc2_rightEnd c len + ![1, 0] ∨ v = jc2_rightEnd c len + ![0, -1]


end Walls
end StatMech
