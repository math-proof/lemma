/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Def.StatisticalMechanics.Code.Sharpness.SharpnessBeta
open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


theorem pBeta_lt_one (J β : ℝ) : pBeta J β < 1 := by
  have := Real.exp_pos (-β * J); unfold pBeta; linarith


theorem pBeta_nonneg {J β : ℝ} (h : 0 ≤ β * J) : 0 ≤ pBeta J β := by
  unfold pBeta
  have : Real.exp (-β * J) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith


theorem pBeta_strictMono {J : ℝ} (hJ : 0 < J) : StrictMono (pBeta J) := by
  intro a b hab
  unfold pBeta
  have : -b * J < -a * J := by nlinarith
  have := Real.exp_lt_exp.mpr this
  linarith


theorem pBeta_toNNReal_le_one (J β : ℝ) : (pBeta J β).toNNReal ≤ 1 :=
  Real.toNNReal_le_one.mpr (le_of_lt (pBeta_lt_one J β))


end Sharpness
end StatMech
