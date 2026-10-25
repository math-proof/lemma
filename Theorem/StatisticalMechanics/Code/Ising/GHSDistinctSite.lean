/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDistinctSite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsQFactor_single_nonneg (B : Finset V) (q : ConfigSpace V) :
    0 ≤ 1 - spinProd B q :=
  one_sub_spinProd_nonneg B q

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem dup_single_pairing_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    isingExpectation G β h (spinProd A) * isingExpectation G β h (spinProd B)
      ≤ isingExpectation G β h (spinProd (A ∆ B)) :=
  gks_second G β h hβ hh A B


end Ising
end StatMech
