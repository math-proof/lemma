module
public import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
public import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
public import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
public import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
public import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part3
open scoped BigOperators
open Filter
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open FK


def FreeFiniteIsingFKXAxisRestrictedCylinderComparison
    (β : ℝ) (hβ : 0 < β) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ N in atTop,
    finiteIsingXAxisTwoPointInVolume β N n =
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n


end Exact3D
end StatMech
