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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


noncomputable def tailPrefixSum (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailCertificate.finitePrefix, W.tailCertificate.weight a


def tailBudget (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.tailBound


noncomputable def tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  W.tailPrefixSum + W.tailBudget


def tailContribution (W : FiniteWitnessPackage (α := α) M) : α → ℝ :=
  W.tailCertificate.weight


noncomputable def tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑' a, W.tailContribution a


def tailSupport (W : FiniteWitnessPackage (α := α) M) : Finset α :=
  W.tailCertificate.tailSupport


def tailSupportCard (W : FiniteWitnessPackage (α := α) M) : ℕ :=
  W.tailSupport.card


def finitePrefixCard (W : FiniteWitnessPackage (α := α) M) : ℕ :=
  W.tailCertificate.finitePrefix.card


noncomputable def tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailSupport, W.tailContribution a


noncomputable def tailEnvelopeSum
    (W : FiniteWitnessPackage (α := α) M) : ℝ :=
  ∑ a ∈ W.tailSupport, W.tailCertificate.envelope a


end FiniteWitnessPackage
end Exact3D
end StatMech
