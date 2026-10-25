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
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def ghsLTComplete (q : ConfigSpace V)
    (st : (v : {v : V // q v = true}) → Bool) : ConfigSpace V :=
  (ghsLSplitEquiv q).symm (st, fun _ => false)


def ghsLUComplete (q : ConfigSpace V)
    (su : (v : {v : V // ¬ q v = true}) → Bool) : ConfigSpace V :=
  (ghsLSplitEquiv q).symm (fun _ => false, su)

end Ising
end StatMech
