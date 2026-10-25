/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Instance.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jeb_imageGraph_support_finite (P : PlanarZ2Subgraph) : (imageGraph P).support.Finite := by
  apply Set.Finite.subset (Set.finite_range P.emb)
  rintro v ⟨w, x, y, hadj, hx, hy⟩; exact ⟨x, hx⟩


end Lattice
end StatMech
