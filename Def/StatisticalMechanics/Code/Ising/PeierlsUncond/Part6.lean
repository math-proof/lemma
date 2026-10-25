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
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part5
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def flipInteriorOnEquiv {n : ℕ} (K : Set (Site d)) :
    ({x // x ∈ box d n} → Bool) ≃ ({x // x ∈ box d n} → Bool) where
  toFun := flipInteriorOn K
  invFun := flipInteriorOn K
  left_inv := flipInteriorOn_involutive K
  right_inv := flipInteriorOn_involutive K

end Ising
end StatMech
