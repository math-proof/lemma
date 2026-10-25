/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def swapPair {n m : ℕ} (hnm : n ≤ m) :
    (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool))
      → (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)) :=
  fun p => (ovrBox hnm p.1 p.2, resBox hnm p.1)


end Ising
end StatMech
