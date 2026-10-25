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
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

def wcl_CorrectColoringResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (f0 g0 : Site 2),
    (hypercubicLattice 2).Adj f0 g0 → wcl_ClosedEven (wcl_cutFlip H f0 g0) →
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ ∧ ¬ (φ f0 ↔ φ g0) ∧
      ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0


end Lattice
end StatMech
