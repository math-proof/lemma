/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation.Part2
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

lemma treeMean_eq_deriv (b : ℕ) (p : ℝ) :
    treeMean b p = deriv (treeGF b p) 1 :=
  (treeGF_hasDerivAt_one b p).deriv.symm


end Percolation
end StatMech
