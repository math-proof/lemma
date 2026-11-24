module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
public import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
public import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part5
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def gec2_GreenDichotomy (n : ℤ) : Prop :=
  (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ ⊆ dualVerticalCrossingEvent (-n) 0 0 (n + 1)


end Universality
end StatMech
