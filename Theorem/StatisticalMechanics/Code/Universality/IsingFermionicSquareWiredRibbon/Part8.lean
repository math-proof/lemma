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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part8
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredConfigurationOfEdges_apply
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredConfigurationOfEdges n F e.1 = true ↔ e ∈ F := by
  simp [fkIsingSquareWiredConfigurationOfEdges]

theorem fkIsingSquareWiredConfigurationOfEdges_insert
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    fkIsingSquareWiredConfigurationOfEdges n (insert e F) =
      setOpen e.1 (fkIsingSquareWiredConfigurationOfEdges n F) := by
  funext f
  by_cases hfe : f = e.1
  · subst f
    simp [fkIsingSquareWiredConfigurationOfEdges]
  · simp [fkIsingSquareWiredConfigurationOfEdges, setOpen, hfe]
    unfold FK.edgeSetConfig
    simp [hfe]

theorem fkIsingSquareWiredConfigurationOfEdges_closed
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    setClosed e.1 (fkIsingSquareWiredConfigurationOfEdges n F) =
      fkIsingSquareWiredConfigurationOfEdges n F := by
  funext f
  by_cases hfe : f = e.1
  · subst f
    have hnot : e.1 ∉ F.image Subtype.val := by simpa using he
    simp [fkIsingSquareWiredConfigurationOfEdges, hnot]
    unfold FK.edgeSetConfig
    simp [hnot]
  · simp [setClosed, hfe]


end
end StatMech.Universality
