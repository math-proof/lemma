/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def arcns_vlshape (x0 y0 x1 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y0] ![x1, y1] :=
  (sw_vertSeg x0 y0 y1).append (sw_horizSeg y1 x0 x1)


end Lattice
end StatMech
