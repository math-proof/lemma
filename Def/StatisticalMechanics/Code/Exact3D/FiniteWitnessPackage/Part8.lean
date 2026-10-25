/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


def with_tailEnvelope_and_tailBudget (W : FiniteWitnessPackage (α := α) M)
    (envelope' : α → ℝ) {tailBound' : ℝ}
    (henvelope_nonneg :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
    (hweight_le :
      ∀ a, a ∈ W.tailCertificate.support →
        a ∉ W.tailCertificate.finitePrefix →
          W.tailCertificate.weight a ≤ envelope' a)
    (henvelope_sum :
      (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix,
        envelope' a) ≤ tailBound') :
    FiniteWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate :=
    W.tailCertificate.with_tailEnvelope_and_tailBound envelope'
      henvelope_nonneg hweight_le henvelope_sum

end FiniteWitnessPackage
end Exact3D
end StatMech
