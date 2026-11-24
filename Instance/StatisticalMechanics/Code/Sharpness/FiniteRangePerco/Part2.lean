module
public import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
public import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part4
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


noncomputable instance (K : FiniteRangeKernel d) (beta : ℝ) :
    IsProbabilityMeasure (frpMeasure K beta) := by
  unfold frpMeasure
  infer_instance


end Sharpness
end StatMech
