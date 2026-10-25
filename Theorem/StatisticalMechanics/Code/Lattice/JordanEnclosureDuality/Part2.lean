/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jed_primalGraph_adj (E : Set (Sym2 (Site 2))) (u w : Site 2) :
    (jed_primalGraph E).Adj u w ↔ (hypercubicLattice 2).Adj u w ∧ s(u, w) ∈ E := Iff.rfl


theorem jed_primalGraph_le (E : Set (Sym2 (Site 2))) : jed_primalGraph E ≤ hypercubicLattice 2 :=
  fun _ _ h => h.1


theorem jed_primalGraph_edgeSet_subset (E : Set (Sym2 (Site 2))) :
    (jed_primalGraph E).edgeSet ⊆ E := by
  intro e he; induction e with
  | h u w => rw [SimpleGraph.mem_edgeSet] at he; exact he.2


end Lattice
end StatMech
