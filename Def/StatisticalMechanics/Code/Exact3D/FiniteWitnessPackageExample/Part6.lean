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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

noncomputable def contributionSplitWitnessPackageCoarserTailEnvelope :
    FiniteWitnessPackage (α := Fin 2) (ToyCriticalModel exampleScale 3) :=
  contributionSplitWitnessPackage.with_tailEnvelope_and_tailBudget
    (fun _ : Fin 2 => (3 : ℝ) / 2)
    (tailBound' := (3 : ℝ))
    (by
      intro a ha hprefix
      norm_num)
    (by
      intro a ha hprefix
      norm_num [contributionSplitWitnessPackage,
        FiniteWitnessPackage.ofContributionSplitFiniteSupport,
        ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
        TailSummabilityExample.exampleSplit])
    (by
      norm_num [contributionSplitWitnessPackage,
        FiniteWitnessPackage.ofContributionSplitFiniteSupport,
        ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn])


end FiniteWitnessPackageExample
end Exact3D
end StatMech
