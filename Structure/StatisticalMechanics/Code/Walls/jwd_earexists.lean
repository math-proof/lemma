/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_earexists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jwd_ExtremeEar (K : Set (Site 2)) (c : Site 2) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  isBoundary : IsBoundaryDart K (leftDart c)
  
  turnLeft : turnZ K (leftDart c) = -1


end Walls
end StatMech
