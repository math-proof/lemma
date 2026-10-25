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
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part7
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsLFibreWeight (β h : ℝ) (q a : ConfigSpace V) : ℝ :=
  isingWeight G β h a * isingWeight G β h (ghsLMate q a)


noncomputable def ghsLFibreMass (β h : ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsLFibreWeight G β h q a


noncomputable def ghsLFibreNumerator (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V,
    ghsLFibreWeight G β h q a * F a (ghsLMate q a)


noncomputable def ghsLFibreExpectation (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ghsLFibreNumerator G β h F q / ghsLFibreMass G β h q


noncomputable def ghsLAgreementProb (β h : ℝ) (q : ConfigSpace V) : ℝ :=
  ghsLFibreMass G β h q / (isingZ G β h) ^ 2

end Ising
end StatMech
