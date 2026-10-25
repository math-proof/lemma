/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

noncomputable def contributionSplitWitnessPackage :
    FiniteWitnessPackage (α := Fin 2) (ToyCriticalModel exampleScale 3) :=
  FiniteWitnessPackage.ofContributionSplitFiniteSupport
    (α := Fin 2) (Case := Unit)
    (ToyCriticalModel exampleScale 3)
    exampleScale (thermal := 3) (by norm_num)
    stableZeroWitness
    TailSummabilityExample.exampleSplit
    (Finset.univ : Finset (Fin 2)) ∅
    (T := TailSummabilityExample.exampleTable)
    (classify := TailSummabilityExample.exampleClassifier)
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (1 : ℝ) / 5)
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    TailSummabilityExample.exampleTotal_zero_off_support
    exampleSplit_total_nonneg
    TailSummabilityExample.exampleSplit_additive
    TailSummabilityExample.exampleFiniteTableUpperBound
    TailSummabilityExample.exampleTailEnvelopeOn
    (by simpa using TailSummabilityExample.exampleTailEnvelopeSum_le)


end FiniteWitnessPackageExample
end Exact3D
end StatMech
