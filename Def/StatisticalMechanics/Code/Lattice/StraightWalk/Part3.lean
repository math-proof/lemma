/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part3
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def sw_lshape (x0 y0 x1 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y0] ![x1, y1] :=
  (sw_horizSeg y0 x0 x1).append (sw_vertSeg x1 y0 y1)


end Lattice
end StatMech
