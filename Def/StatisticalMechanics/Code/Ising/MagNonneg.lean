/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def spinBCF (x : Site d) : ConfigSpace (Site d) →ᵇ ℝ :=
  ⟨⟨fun ω => spin ω x, continuous_spinObs x⟩,
    ⟨2, fun ω ω' => by
      have h1 := spinObs_le_one x ω
      have h2 := spinObs_le_one x ω'
      calc dist (spin ω x) (spin ω' x) ≤ ‖spin ω x‖ + ‖spin ω' x‖ := dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by ring⟩⟩

end Ising
end StatMech
