/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation.Part4
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

lemma extinctionProb_mem (b : ℕ) (p : ℝ) : extinctionProb b p ∈ fixedSet b p :=
  (fixedSet_isClosed b p).csInf_mem (fixedSet_nonempty b p) (fixedSet_bddBelow b p)

lemma extinctionProb_isFixed (b : ℕ) (p : ℝ) :
    treeGF b p (extinctionProb b p) = extinctionProb b p :=
  (extinctionProb_mem b p).2

lemma extinctionProb_mem_Icc (b : ℕ) (p : ℝ) : extinctionProb b p ∈ Icc (0 : ℝ) 1 :=
  (extinctionProb_mem b p).1

lemma extinctionProb_nonneg (b : ℕ) (p : ℝ) : 0 ≤ extinctionProb b p :=
  (extinctionProb_mem_Icc b p).1

lemma extinctionProb_le_one (b : ℕ) (p : ℝ) : extinctionProb b p ≤ 1 :=
  (extinctionProb_mem_Icc b p).2


end Percolation
end StatMech
