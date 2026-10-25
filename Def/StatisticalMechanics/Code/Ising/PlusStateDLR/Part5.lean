/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[reducible] def outsideInvariantMS {E : Type*} (Λ : Set E) : MeasurableSpace (ConfigSpace E) where
  MeasurableSet' s := ∀ ω ω' : ConfigSpace E, (∀ x ∉ Λ, ω x = ω' x) → (ω ∈ s ↔ ω' ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl s hs ω ω' h := by simp only [Set.mem_compl_iff]; rw [hs ω ω' h]
  measurableSet_iUnion f hf ω ω' h := by
    simp only [Set.mem_iUnion]; exact exists_congr (fun i => hf i ω ω' h)


end Ising
end StatMech
