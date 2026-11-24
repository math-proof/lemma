module
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part3
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def shk_restrictedSusceptibility (p : NNReal) (hp : p ≤ 1)
    (Lam : Finset (Site d)) (u : Site d) : ℝ :=
  ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
    (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x})


end Sharpness
end StatMech
