/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def ConnectedContourCountBound (d n : ℕ) (β : ℝ) : Prop :=
  ∑ K ∈ connClusterFamily (d := d) n,
      Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ))
    ≤ peierlsBound d β


end Ising
end StatMech
