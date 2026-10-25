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
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def ovrBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    {x // x ∈ box d m} → Bool :=
  fun x => if hn : (x : Site d) ∈ box d n then τ ⟨x, hn⟩ else σ x


noncomputable def resBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) : {x // x ∈ box d n} → Bool :=
  fun x => σ ⟨x, box_mono d hnm x.2⟩


end Ising
end StatMech
