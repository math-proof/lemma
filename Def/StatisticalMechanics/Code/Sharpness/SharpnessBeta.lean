/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


noncomputable def pBeta (J β : ℝ) : ℝ := 1 - Real.exp (-β * J)


end Sharpness
end StatMech
