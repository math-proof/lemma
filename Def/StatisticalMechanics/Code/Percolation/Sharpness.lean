/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.Sharpness
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def crossProbReal (d n : ℕ) (t : ℝ) : ℝ :=
  if ht : 0 ≤ t ∧ t ≤ 1 then crossProb d t.toNNReal (Real.toNNReal_le_one.mpr ht.2) n else 0


end Percolation
end StatMech
