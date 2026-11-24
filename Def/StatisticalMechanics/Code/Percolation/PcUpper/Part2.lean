module
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpper
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped NNReal ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def PcContourBound (p : NNReal) (hp : p ≤ 1) : Prop :=
  1 - theta 2 p hp ≤ pcUpperBound (p : ℝ)


end Percolation
end StatMech
