/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part7


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalProjectionAll_injective
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalProjectionAll R level walkLength start
        hstart hlevel hgap) := by
  intro a b hab
  have hh : horizontalRightCode a.2.1.1.1.reflectPrefix.steps =
      horizontalRightCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.2.1.1.1.reflectPrefix.steps =
      verticalCode b.2.1.1.1.reflectPrefix.steps :=
    congrArg (fun z => z.2.1) hab
  have hsteps : a.2.1.1.1.reflectPrefix.steps =
      b.2.1.1.1.reflectPrefix.steps :=
    horizontalRightCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.2.1.1.1 a.2.1.1.2.2.1)
      (reflectPrefix_valid b.2.1.1.1 b.2.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.2.1.1.1 a.2.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.2.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.2.1.1.1 b.2.1.1.2.1)
  have hsplits : a.2.1.1.1.reflectPrefix =
      b.2.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
    cases ha : a.2.1.1.1 with
    | mk ab aa ahit =>
      cases hb : b.2.1.1.1 with
      | mk bb ba bhit =>
        have hreflect : Function.Injective reflectIncrement := by
          intro x y hxy
          apply Prod.ext
          · have hx := congrArg Prod.fst hxy
            simp [reflectIncrement] at hx
            linarith
          · simpa [reflectIncrement] using congrArg Prod.snd hxy
        have hbeforeMap := congrArg
          (fun w : IsingDiagonalWalkHitSplit
            (reflectedEndpoint (level : Int) start) (level : Int) => w.before)
          hsplits
        simp only [ha, hb, reflectPrefix_before] at hbeforeMap
        have hbefore : ab = bb :=
          (Function.Injective.list_map hreflect) hbeforeMap
        have hafterRaw := congrArg
          (fun w : IsingDiagonalWalkHitSplit
            (reflectedEndpoint (level : Int) start) (level : Int) => w.after)
          hsplits
        simp only [ha, hb, reflectPrefix_after] at hafterRaw
        have hafter : aa = ba := hafterRaw
        subst bb
        subst ba
        rfl
  have htarget : a.1 = b.1 := by
    have haend := a.2.1.1.2.2.2.2
    have hbend := b.2.1.1.2.2.2.2
    rw [← haend, ← hbend, horiginal]
  cases a with
  | mk atarget aw =>
    cases b with
    | mk btarget bw =>
      dsimp at htarget horiginal
      subst btarget
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact horiginal

end IsingDiagonalWalkHitSplit
end StatMech.Universality
