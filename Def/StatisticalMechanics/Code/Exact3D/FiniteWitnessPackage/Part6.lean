module
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
public import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


def retarget {κ : Type*} (W : FiniteWitnessPackage (α := α) M)
    (N : CriticalModel κ) : FiniteWitnessPackage (α := α) N where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate

end FiniteWitnessPackage
end Exact3D
end StatMech
