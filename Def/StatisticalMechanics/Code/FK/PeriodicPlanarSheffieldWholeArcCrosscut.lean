/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace Lattice

open ContinuousRectangleCrossing


def halfPlaneReturnPath (alpha c d : Int) (hcd : c <= d) :
    (hypercubicLattice 2).Walk ![alpha, d] ![alpha, c] :=
  let top : (hypercubicLattice 2).Walk ![alpha, d] ![alpha - 1, d] :=
    ((jec_hsegRight d (alpha - 1) 1).copy rfl
      (by ext i; fin_cases i <;> simp)).reverse
  let side : (hypercubicLattice 2).Walk ![alpha - 1, d] ![alpha - 1, c] :=
    ((jec_vsegUp (alpha - 1) c (d - c).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let bottom : (hypercubicLattice 2).Walk ![alpha - 1, c] ![alpha, c] :=
    (jec_hsegRight c (alpha - 1) 1).copy rfl
      (by ext i; fin_cases i <;> simp)
  top.append (side.append bottom)


end Lattice
end StatMech
