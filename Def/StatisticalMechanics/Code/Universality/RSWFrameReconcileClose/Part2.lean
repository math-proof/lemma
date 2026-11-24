module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
public import Theorem.StatisticalMechanics.Code.Universality.Rot90Reindex
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
public import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part2
open Set SimpleGraph MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def rfr_MatchedPlanarDuality (n : ℤ) : Prop :=
  (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 (n + 1) 0 n


end Universality
end StatMech
