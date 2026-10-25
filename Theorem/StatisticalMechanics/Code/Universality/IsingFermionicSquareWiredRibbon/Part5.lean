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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part5
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Function.Bijective
      (fkIsingSquareWiredBlackBoundaryCycleToComponent n hn omega) := by
  classical
  constructor
  · intro A B hAB
    induction A using Quot.ind with
    | _ x =>
      induction B using Quot.ind with
      | _ y =>
        apply Quot.sound
        apply (fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
          n hn omega x y).2
        apply SimpleGraph.ConnectedComponent.exact
        exact hAB
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ x =>
      by_cases hx : fkIsingSquareWiredCarrierColor n x = false
      · exact ⟨Quot.mk _ (⟨x, hx⟩ : FKIsingSquareWiredBlackCarrier n), rfl⟩
      · have hblack : fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionEquiv n hn omega x) = false := by
          have hne := fkIsingSquareWiredCarrierColor_transition_ne n hn omega x
          generalize hc : fkIsingSquareWiredCarrierColor n x = c at hx hne
          generalize ht : fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionEquiv n hn omega x) = t at hne ⊢
          cases c <;> cases t <;> simp_all
        let b : FKIsingSquareWiredBlackCarrier n :=
          ⟨fkIsingSquareWiredTransitionEquiv n hn omega x, hblack⟩
        refine ⟨Quot.mk _ b, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        apply Adj.reachable
        rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
        apply Or.inl
        change x = fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredTransitionMate n hn omega x)
        exact (fkIsingSquareWiredTransitionMate_involutive n hn omega x).symm


theorem permCycleCount_fkIsingSquareWiredBlackBoundaryPerm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.permCycleCount
        (fkIsingSquareWiredBlackBoundaryPerm n hn omega) =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent := by
  classical
  rw [← StatMech.FrontierA.natCard_permCycleClass]
  exact Nat.card_congr (Equiv.ofBijective
    (fkIsingSquareWiredBlackBoundaryCycleToComponent n hn omega)
    (fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective n hn omega))

end
end StatMech.Universality
