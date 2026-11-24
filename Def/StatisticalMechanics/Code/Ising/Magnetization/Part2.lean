module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Theorem.StatisticalMechanics.Code.Ising.Magnetization.Part2
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


def positiveMagnetizationSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ 0 < magnetization d β}

end Ising
end StatMech
