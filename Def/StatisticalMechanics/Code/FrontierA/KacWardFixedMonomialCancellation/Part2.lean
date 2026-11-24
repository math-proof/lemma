module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
public import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part5
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSupport
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFixedMonomialCancellation
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Finset


noncomputable def kwFixedOrbitExponentLoops
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} (selected : Dart) (reverse : Dart -> Dart)
    (exponent : Sym2 Dart →₀ ℕ) : Finset (Fin n -> Dart) :=
  (StatMech.Onsager.ons_loopSetBoth (n := n)
    selected (reverse selected)).filter fun loop =>
      kwLoopOrbitExponent reverse loop = exponent


end StatMech.FrontierA
