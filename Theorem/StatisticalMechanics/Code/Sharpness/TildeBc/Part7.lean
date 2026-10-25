/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part8
open MeasureTheory
open scoped BigOperators NNReal
open Finset


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}


@[simp]
theorem mem_tildeBetaCIsingSet {d : ℕ} {β : ℝ} :
    β ∈ tildeBetaCIsingSet d ↔
      0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1 :=
  Iff.rfl


end Sharpness
end StatMech
