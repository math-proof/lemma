/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part5
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def isingPMF (β h : ℝ) : PMF (ConfigSpace V) :=
  PMF.ofFintype (fun s => ENNReal.ofReal (isingProb G β h s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => isingProb_nonneg G β h s),
      isingProb_sum_eq_one G β h]
    simp)

end Ising
end StatMech
