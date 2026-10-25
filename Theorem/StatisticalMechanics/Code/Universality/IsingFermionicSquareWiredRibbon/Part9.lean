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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredRibbonBoundaryPerm_insert_right
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm (insert e F) =
      (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F *
        fkIsingSquareWiredBlackLocalSwap n e := by
  let R := fkIsingSquareWiredRibbonSystem n hn
  change R.boundaryPerm (insert e F) =
    R.boundaryPerm F * R.edgeFlip e
  have hcomm : Commute (R.edgeFlip e) (R.partialEdgeFlip F) := by
    unfold StatMech.FrontierA.RibbonPermutationSystem.partialEdgeFlip
    apply Finset.noncommProd_commute
    intro f hf
    exact R.edgeFlip_commute e f fun h => he (h ▸ hf)
  rw [StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm,
    R.partialEdgeFlip_insert F e (by simpa using he),
    StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm]
  rw [hcomm.eq]
  simp only [mul_assoc]

theorem fkIsingSquareWiredRibbonSystem_boundaryPerm
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F =
      fkIsingSquareWiredBlackBoundaryPerm n hn
        (fkIsingSquareWiredConfigurationOfEdges n F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm_empty]
      rfl
  | @insert e F he ih =>
      calc
        (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm (insert e F) =
            (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F *
              fkIsingSquareWiredBlackLocalSwap n e :=
          fkIsingSquareWiredRibbonBoundaryPerm_insert_right n hn F e he
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (fkIsingSquareWiredConfigurationOfEdges n F) *
                fkIsingSquareWiredBlackLocalSwap n e := by rw [ih]
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (setClosed e.1 (fkIsingSquareWiredConfigurationOfEdges n F)) *
                fkIsingSquareWiredBlackLocalSwap n e := by
          rw [fkIsingSquareWiredConfigurationOfEdges_closed n F e he]
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (setOpen e.1 (fkIsingSquareWiredConfigurationOfEdges n F)) :=
          (fkIsingSquareWiredBlackBoundaryPerm_setOpen n hn _ e).symm
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (fkIsingSquareWiredConfigurationOfEdges n (insert e F)) := by
          rw [fkIsingSquareWiredConfigurationOfEdges_insert n F e he]

theorem fkIsingSquareWiredRibbonSystem_boundaryComponents
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryComponents F =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (fkIsingSquareWiredConfigurationOfEdges n F)).ConnectedComponent := by
  unfold StatMech.FrontierA.RibbonPermutationSystem.boundaryComponents
  rw [fkIsingSquareWiredRibbonSystem_boundaryPerm,
    permCycleCount_fkIsingSquareWiredBlackBoundaryPerm]

end
end StatMech.Universality
