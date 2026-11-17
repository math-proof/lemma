/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation

@[expose] public section

open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

noncomputable def treeMean (b : ℕ) (p : ℝ) : ℝ := (b : ℝ) * p

end Percolation
end StatMech
