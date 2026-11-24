module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part4
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice


noncomputable def pcSummandTwo (p : ℝ) (ℓ : ℕ) : ℝ := (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p) ^ ℓ)

end Percolation
end StatMech
