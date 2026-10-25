/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWired_cycle_turn_mod_sixteen_of_simplePolygon
    {m : Nat} [NeZero m]
    (polygon : StatMech.FrontierA.KWFiniteSimplePolygon m)
    (turn : Int)
    (hphase : Complex.exp
        (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) =
      StatMech.FrontierA.kwVectorPhaseCycle polygon.edgeList) :
    turn ≡ 8 [ZMOD 16] := by
  apply int_eighth_turn_mod_sixteen_of_exp_eq_neg_one
  rw [hphase]
  exact StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_adaptive polygon


end
end StatMech.Universality
