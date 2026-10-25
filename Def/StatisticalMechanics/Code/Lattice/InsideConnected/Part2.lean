/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Set (Site 2) :=
  {z | (offSupport Vc).Reachable seed z}

end Lattice
end StatMech
