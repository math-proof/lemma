/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Ising.Gibbs.Part4
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


lemma isingZ_pos (β h : ℝ) : 0 < isingZ G β h := by
  unfold isingZ
  apply Finset.sum_pos
  · intro s _; exact isingWeight_pos G β h s
  · exact Finset.univ_nonempty

lemma isingZ_ne_zero (β h : ℝ) : isingZ G β h ≠ 0 := (isingZ_pos G β h).ne'


end Ising
end StatMech
