/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Def.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mci_kingAdj_symm : Symmetric mci_kingAdj := by
  rintro u v ⟨h0, h1, hne⟩
  refine ⟨?_, ?_, hne.symm⟩
  · rw [← Int.natAbs_neg, neg_sub]; exact h0
  · rw [← Int.natAbs_neg, neg_sub]; exact h1

theorem mci_kingAdj_irrefl : ∀ u, ¬ mci_kingAdj u u := by
  rintro u ⟨_, _, hne⟩; exact hne rfl


end Lattice
end StatMech
