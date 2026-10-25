/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation.Part3
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

lemma one_mem_fixedSet (b : ℕ) (p : ℝ) : (1 : ℝ) ∈ fixedSet b p :=
  ⟨⟨zero_le_one, le_refl 1⟩, by simp⟩

lemma fixedSet_nonempty (b : ℕ) (p : ℝ) : (fixedSet b p).Nonempty :=
  ⟨1, one_mem_fixedSet b p⟩

lemma fixedSet_bddBelow (b : ℕ) (p : ℝ) : BddBelow (fixedSet b p) :=
  ⟨0, fun _ hs => hs.1.1⟩

lemma fixedSet_isClosed (b : ℕ) (p : ℝ) : IsClosed (fixedSet b p) :=
  isClosed_Icc.inter (isClosed_eq (treeGF_continuous b p) continuous_id)


end Percolation
end StatMech
