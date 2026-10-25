/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part3
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredCarrierColor_boundaryStep
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBoundaryStep n hn omega x) =
      fkIsingSquareWiredCarrierColor n x := by
  have hT := fkIsingSquareWiredCarrierColor_transition_ne n hn omega x
  have hI := fkIsingSquareWiredCarrierColor_completedIncidence_ne n
    (fkIsingSquareWiredTransitionEquiv n hn omega x)
  simp only [fkIsingSquareWiredBoundaryStep, Equiv.trans_apply] at hI ⊢
  generalize hx : fkIsingSquareWiredCarrierColor n x = a at hT ⊢
  generalize ht : fkIsingSquareWiredCarrierColor n
    (fkIsingSquareWiredTransitionEquiv n hn omega x) = b at hT hI
  generalize hi : fkIsingSquareWiredCarrierColor n
    (fkIsingSquareWiredCompletedIncidenceEquiv n
      (fkIsingSquareWiredTransitionEquiv n hn omega x)) = c at hI ⊢
  cases a <;> cases b <;> cases c <;> simp_all


end
end StatMech.Universality
