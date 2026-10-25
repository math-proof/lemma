/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_earanchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jwd_earexists
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc_EarAnchor (K : Set (Site 2)) (c : Site 2) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  isBoundary : IsBoundaryDart K (leftDart c)
  
  turnLeft : turnZ K (leftDart c) = -1
  
  neighbor_right_or_down :
    ∀ v ∈ K, (hypercubicLattice 2).Adj v c → v = c + ![1, 0] ∨ v = c + ![0, -1]


end Walls
end StatMech
