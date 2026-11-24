module
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
public import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
public import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part5
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


@[simp] theorem certificate_scale_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.fixedPointData.fixedPoint = W.fixedPoint :=
  rfl


theorem certificate_predictedExponent_eq
    (W : FiniteWitnessPackage (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl


end FiniteWitnessPackage
end Exact3D
end StatMech
