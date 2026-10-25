/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring
open SimpleGraph Set


namespace StatMech

namespace Lattice

def wcl_ClosedEven (flip : Site 2 → Site 2 → Prop) : Prop :=
  ∀ {x : Site 2} (w : (hypercubicLattice 2).Walk x x), Even (wcl_flipCount flip w)


end Lattice
end StatMech
