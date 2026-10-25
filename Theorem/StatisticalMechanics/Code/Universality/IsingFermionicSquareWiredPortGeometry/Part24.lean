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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part25


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredPortIntPosition_localMate_exact_step
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortIntPosition n
        (FKIsingMedialDart.localMate omega d) =
      fkIsingSquareWiredPortIntPosition n d +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredLocalStepIndex omega d) := by
  rcases d with ⟨e, side⟩
  cases homega : omega e.1 <;> cases side
  all_goals simp only [FKIsingMedialDart.localMate, homega]
  all_goals
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
      simp [fkIsingSquareWiredLocalStepIndex,
        fkIsingSquareWiredPortIntPosition, homega, haxis,
        fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] <;> omega

end
end StatMech.Universality
