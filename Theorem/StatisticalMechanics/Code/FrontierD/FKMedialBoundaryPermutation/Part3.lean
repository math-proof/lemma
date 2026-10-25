/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
open SimpleGraph Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


theorem fkMedialBlackBoundaryCycleToLoop_bijective
    (pairing : FKMedialLoopPairing T) :
    Function.Bijective (fkMedialBlackBoundaryCycleToLoop pairing) := by
  classical
  constructor
  · intro A B hAB
    induction A using Quot.ind with
    | _ d =>
      induction B using Quot.ind with
      | _ e =>
        apply Quot.sound
        apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing d e).2
        apply SimpleGraph.ConnectedComponent.exact
        exact hAB
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ d =>
      by_cases hd : fkMedialCheckerColor d = false
      · refine ⟨Quot.mk _ (⟨d, hd⟩ : FKMedialBlackDart T), rfl⟩
      · have hlocal : fkMedialCheckerColor
            (fkMedialLocalMate pairing d) = false := by
          have hne := fkMedialCheckerColor_localMate_ne pairing d
          generalize hc : fkMedialCheckerColor d = c at hd hne
          generalize hl : fkMedialCheckerColor
            (fkMedialLocalMate pairing d) = l at hne ⊢
          cases c <;> cases l <;> simp_all
        let b : FKMedialBlackDart T :=
          ⟨fkMedialLocalMate pairing d, hlocal⟩
        refine ⟨Quot.mk _ b, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        exact (show (fkMedialLoopGraph T pairing).Adj
            (fkMedialLocalMate pairing d) d by
          rw [fkMedialLoopGraph_adj_iff]
          left
          rw [fkMedialLocalMate_involutive]).reachable


theorem permCycleCount_fkMedialBlackBoundaryPerm
    (pairing : FKMedialLoopPairing T) :
    StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) =
      fkMedialLoopCount T pairing := by
  classical
  rw [← StatMech.FrontierA.natCard_permCycleClass]
  unfold fkMedialLoopCount
  exact Nat.card_congr (Equiv.ofBijective
    (fkMedialBlackBoundaryCycleToLoop pairing)
    (fkMedialBlackBoundaryCycleToLoop_bijective pairing))

end StatMech.FrontierD
