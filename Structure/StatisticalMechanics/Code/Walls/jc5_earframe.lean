/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
import Theorem.StatisticalMechanics.Code.Walls.jc5_earframe.Part2
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc5_EarFrame (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  
  isFramedRun : jc2_RunFrame K c len
  
  ear_up_out : jc5_earUp c len ∉ K
  
  ear_right_out : jc5_earRight c len ∉ K
  

  ear_shelf_in : jc5_earShelf c len ∈ K


end Walls
end StatMech
