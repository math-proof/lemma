/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFixedMonomialCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part5
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSupport
open scoped BigOperators


namespace StatMech.FrontierA

open Finset


noncomputable def kwLoopOrbitExponent
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} (reverse : Dart -> Dart) (loop : Fin n -> Dart) :
    Sym2 Dart →₀ ℕ :=
  ∑ k, Finsupp.single s(loop k, reverse (loop k)) 1


end StatMech.FrontierA
