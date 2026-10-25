/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part5
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

def subcriticalSetTree (b : ℕ) : Set ℝ := {p | p ∈ Icc (0 : ℝ) 1 ∧ survivalProb b p = 0}


noncomputable def treePc (b : ℕ) : ℝ := sSup (subcriticalSetTree b)

end Percolation
end StatMech
