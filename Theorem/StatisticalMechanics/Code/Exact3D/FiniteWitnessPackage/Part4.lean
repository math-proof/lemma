module
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
public import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
public import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part4
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


theorem fixedPoint_eq (W : FiniteWitnessPackage (α := α) M) :
    W.rgMap.map W.fixedPoint = W.fixedPoint := by
  apply Prod.ext
  · simp [rgMap, fixedPoint]
  · simpa [rgMap, fixedPoint] using W.stable.fixedPoint_isFixed


end FiniteWitnessPackage
end Exact3D
end StatMech
