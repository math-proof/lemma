/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Ising.Gibbs.Part5
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


lemma isingProb_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingProb G β h s :=
  div_nonneg (isingWeight_nonneg G β h s) (isingZ_pos G β h).le


lemma isingProb_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingProb G β h s :=
  div_pos (isingWeight_pos G β h s) (isingZ_pos G β h)


lemma isingProb_sum_eq_one (β h : ℝ) : ∑ s : ConfigSpace V, isingProb G β h s = 1 := by
  unfold isingProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (isingZ_ne_zero G β h)]
  rfl


end Ising
end StatMech
