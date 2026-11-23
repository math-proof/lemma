/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part2

@[expose] public section

open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

def fixedSet (b : ℕ) (p : ℝ) : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ treeGF b p s = s}

end Percolation
end StatMech
