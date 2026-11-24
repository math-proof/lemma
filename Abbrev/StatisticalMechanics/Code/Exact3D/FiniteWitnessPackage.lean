module
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
public import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
public import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part2
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


abbrev State (W : FiniteWitnessPackage (α := α) M) : Type :=
  ℝ × (Fin W.nStable → ℝ)


abbrev hamiltonian (W : FiniteWitnessPackage (α := α) M) :
    EffectiveHamiltonian where
  carrier := W.State


end FiniteWitnessPackage
end Exact3D
end StatMech
