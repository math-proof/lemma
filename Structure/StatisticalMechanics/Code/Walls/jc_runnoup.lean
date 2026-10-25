/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc_IsTopRowRun (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  len_nonneg : 0 ≤ len
  
  run_mem : ∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, 0]) ∈ K
  
  right_stop : (c + ![len + 1, 0]) ∉ K


end Walls
end StatMech
