module
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
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


noncomputable def shk_translateFinset (g : Multiplicative (Site d))
    (S : Finset (Site d)) : Finset (Site d) :=
  S.image (fun x => g • x)

end Sharpness
end StatMech
