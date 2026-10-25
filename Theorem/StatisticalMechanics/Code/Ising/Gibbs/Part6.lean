/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Ising.Gibbs.Part6
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] lemma isingPMF_apply (β h : ℝ) (s : ConfigSpace V) :
    isingPMF G β h s = ENNReal.ofReal (isingProb G β h s) := rfl

end Ising
end StatMech
