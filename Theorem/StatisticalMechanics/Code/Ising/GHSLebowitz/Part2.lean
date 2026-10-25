/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ghsLAgreement_mate (q a : ConfigSpace V) :
    ghsLAgreement (V := V) a (ghsLMate q a) = q := by
  funext v
  unfold ghsLAgreement ghsLMate
  by_cases hq : q v <;> cases a v <;> simp [hq]

@[simp] theorem ghsLMate_agreement (a b : ConfigSpace V) :
    ghsLMate (ghsLAgreement (V := V) a b) a = b := by
  funext v
  unfold ghsLAgreement ghsLMate
  cases ha : a v <;> cases hb : b v <;> simp [ha, hb]


theorem ghsL_uvar_mate (q a : ConfigSpace V) (v : V) :
    uvar a (ghsLMate q a) v = if q v then 0 else spin a v := by
  unfold uvar ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]


theorem ghsL_tvar_mate (q a : ConfigSpace V) (v : V) :
    tvar a (ghsLMate q a) v = if q v then spin a v else 0 := by
  unfold tvar ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]


end Ising
end StatMech
