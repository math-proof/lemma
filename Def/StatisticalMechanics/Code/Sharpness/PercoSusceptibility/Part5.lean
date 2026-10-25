/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part4
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def shk_twoPointProb (p : ℝ≥0) (hp : p ≤ 1)
    (x : Site d) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
    {omega | Connected d omega (origin d) x}


end Sharpness
end StatMech
