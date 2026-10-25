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
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part6
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsL_sum_pair_xnor (F : ConfigSpace V → ConfigSpace V → ℝ) :
    (∑ a : ConfigSpace V, ∑ b : ConfigSpace V, F a b)
      = ∑ q : ConfigSpace V, ∑ a : ConfigSpace V, F a (ghsLMate q a) := by
  calc
    (∑ a : ConfigSpace V, ∑ b : ConfigSpace V, F a b) =
        ∑ p : ConfigSpace V × ConfigSpace V, F p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : ConfigSpace V × ConfigSpace V => F p.1 p.2)).symm
    _ = ∑ p : ConfigSpace V × ConfigSpace V,
        (fun qa => F qa.2 (ghsLMate qa.1 qa.2)) ((ghsLXnorEquiv (V := V)) p) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [ghsLXnorEquiv]
    _ = ∑ qa : ConfigSpace V × ConfigSpace V,
        F qa.2 (ghsLMate qa.1 qa.2) :=
      Equiv.sum_comp (ghsLXnorEquiv (V := V))
        (fun qa => F qa.2 (ghsLMate qa.1 qa.2))
    _ = ∑ q : ConfigSpace V, ∑ a : ConfigSpace V, F a (ghsLMate q a) :=
      Fintype.sum_prod_type (fun qa : ConfigSpace V × ConfigSpace V =>
        F qa.2 (ghsLMate qa.1 qa.2))


end Ising
end StatMech
