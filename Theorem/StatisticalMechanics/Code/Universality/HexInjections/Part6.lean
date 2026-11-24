module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Def.StatisticalMechanics.Code.Universality.HexInjections.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexHighestCutSplit_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexSplitAt (hexCutPos a h0)) :=
  hexSplitAt_injective _


end StatMech.Universality
