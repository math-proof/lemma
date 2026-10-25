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
import Def.StatisticalMechanics.Code.FrontierA.KacWardFixedMonomialCancellation
open scoped BigOperators


namespace StatMech.FrontierA

open Finset


theorem kwLoopOrbitExponent_surgery
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n] (selected : Dart) (reverse : Dart -> Dart)
    (hreverse : Function.Involutive reverse) (loop : Fin n -> Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = reverse selected) :
    kwLoopOrbitExponent reverse
        (StatMech.Onsager.ons_surgery selected reverse loop) =
      kwLoopOrbitExponent reverse loop := by
  unfold kwLoopOrbitExponent
  exact StatMech.Onsager.ons_sum_surgery_invariant
    selected reverse hreverse
    (fun dart => Finsupp.single s(dart, reverse dart) 1)
    (fun dart => by
      change Finsupp.single
        s(reverse dart, reverse (reverse dart)) 1 =
          Finsupp.single s(dart, reverse dart) 1
      rw [hreverse, Sym2.eq_swap])
    loop hboth


end StatMech.FrontierA
