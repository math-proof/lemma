module
public import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
public import Instance.StatisticalMechanics.Code.Sharpness.FiniteRangePerco
open MeasureTheory
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


noncomputable def frpEdgeParam (K : FiniteRangeKernel d) (beta : ℝ)
    (e : Sym2 (Site d)) : NNReal :=
  Real.toNNReal (1 - Real.exp (-beta * frpEdgeCoupling K e))

end Sharpness
end StatMech
