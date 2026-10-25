/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Ising.Gibbs.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in

lemma isingWeight_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingWeight G β h s :=
  Real.exp_pos _

omit [DecidableEq V] in
lemma isingWeight_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingWeight G β h s :=
  (isingWeight_pos G β h s).le


end Ising
end StatMech
