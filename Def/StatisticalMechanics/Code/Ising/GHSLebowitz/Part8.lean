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
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part8
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsLFibreUU (β h : ℝ) (o x : V) (q : ConfigSpace V) : ℝ :=
  ghsLFibreExpectation G β h (fun a b => uvar a b o * uvar a b x) q


noncomputable def ghsLFibreT (β h : ℝ) (y : V) (q : ConfigSpace V) : ℝ :=
  ghsLFibreExpectation G β h (fun a b => tvar a b y) q


noncomputable def ghsLUExpectation (β : ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsLUWeight G β q a * F a) /
    ∑ a : ConfigSpace V, ghsLUWeight G β q a


noncomputable def ghsLTExpectation (β h : ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsLTWeight G β h q a * F a) /
    ∑ a : ConfigSpace V, ghsLTWeight G β h q a

end Ising
end StatMech
