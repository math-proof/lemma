/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CollaredWalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
open SimpleGraph


namespace StatMech.Lattice

open StatMech.RSW.Box

noncomputable section

def horizontalWallExtension (alpha beta : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y) :
    (hypercubicLattice 2).Walk ![alpha, x 1] ![beta, y 1] :=
  let W' : (hypercubicLattice 2).Walk
      ![x 0, x 1] ![y 0, y 1] := W.copy (by
        ext i
        fin_cases i <;> simp) (by
        ext i
        fin_cases i <;> simp)
  ((sw_horizSeg (x 1) alpha (x 0)).append W').append
    (sw_horizSeg (y 1) (y 0) beta)


end
end StatMech.Lattice
