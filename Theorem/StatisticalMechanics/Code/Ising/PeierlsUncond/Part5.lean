/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part5
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma flipInteriorOn_involutive {n : ℕ} (K : Set (Site d))
    (τ : {x // x ∈ box d n} → Bool) : flipInteriorOn K (flipInteriorOn K τ) = τ := by
  funext x; unfold flipInteriorOn; by_cases hx : (x : Site d) ∈ K <;> simp [hx]


end Ising
end StatMech
