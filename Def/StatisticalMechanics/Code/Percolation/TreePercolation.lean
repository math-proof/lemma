/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

noncomputable def binomialOffspringPMF (b : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (b.choose k : ℝ) * p ^ k * (1 - p) ^ (b - k)


noncomputable def treeGF (b : ℕ) (p : ℝ) (s : ℝ) : ℝ := (1 - p + p * s) ^ b

end Percolation
end StatMech
