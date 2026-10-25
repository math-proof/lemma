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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part27


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredForwardRingStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredForwardRingStepWord n hn d ≠ [] := by
  have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n
    (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d))
    (fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d))
  intro hnil
  have hlen := congrArg List.length hnil
  simp [fkIsingSquareWiredForwardRingStepWord] at hlen
  rcases hcases with h | h | h <;> simp [h] at hlen

theorem fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredOrdinaryBondStepWord n hn d ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
    List.length_ofFn] at hlen
  split at hlen <;>
    have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n
      (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d))
      (fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d)) <;>
    rcases hcases with h | h | h <;> simp [h] at hlen


end
end StatMech.Universality
