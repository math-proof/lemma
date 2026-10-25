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
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_extremeCell_up_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![0, 1] ∉ K :=
  extremeCell_up_nmem K c hc


theorem jc_extremeCell_left_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![-1, 0] ∉ K :=
  extremeCell_left_nmem K c hc


theorem jc_extremeCell_neighbor_right_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![0, -1] :=
  extremeCell_neighbor_right_or_down K c v hc hv hadj


end Walls
end StatMech
