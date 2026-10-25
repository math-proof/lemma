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
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[reducible]
noncomputable def jeb_induceLF {V : Type*} (H : SimpleGraph V) [SimpleGraph.LocallyFinite H]
    (s : Set V) : SimpleGraph.LocallyFinite (H.induce s) := by
  classical
  intro v
  rw [SimpleGraph.neighborSet_induce]
  apply Set.Finite.fintype
  apply Set.Finite.preimage (Function.Injective.injOn Subtype.coe_injective)
  exact (H.neighborSet ↑v).toFinite


end Lattice
end StatMech
