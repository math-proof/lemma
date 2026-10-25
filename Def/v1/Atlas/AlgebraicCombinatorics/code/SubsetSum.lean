/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLatticeSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QBinomial
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QBinomial.Part2
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false

open SpernerProperty YoungLattice YoungLattice.Lmn Finset


namespace SubsetSum

noncomputable def subsetSumCount (k : ℕ) (S : Finset ℝ) (α : ℝ) : ℕ :=
  ((powersetCard k S).filter (fun T => T.sum id = α)).card

def iccNat (n : ℕ) : Finset ℕ := Finset.Icc 1 n

def subsetSumCountNat (k n α : ℕ) : ℕ :=
  ((powersetCard k (iccNat n)).filter (fun T => T.sum id = α)).card

end SubsetSum
