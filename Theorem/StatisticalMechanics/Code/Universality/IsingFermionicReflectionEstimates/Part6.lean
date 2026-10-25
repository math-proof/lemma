/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part6


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalFirstHitFamily_projection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalProjection R level walkLength start target
        hstart hlevel hgap) := by
  intro a b hab
  have hh : horizontalRightCode a.1.1.1.reflectPrefix.steps =
      horizontalRightCode b.1.1.1.reflectPrefix.steps := by
    exact congrArg (fun z => z.1.1) hab
  have hv : verticalCode a.1.1.1.reflectPrefix.steps =
      verticalCode b.1.1.1.reflectPrefix.steps := by
    exact congrArg (fun z => z.2.1) hab
  have hsteps : a.1.1.1.reflectPrefix.steps =
      b.1.1.1.reflectPrefix.steps :=
    horizontalRightCode_verticalCode_injective_of_valid
      (reflectPrefix_valid a.1.1.1 a.1.1.2.2.1)
      (reflectPrefix_valid b.1.1.1 b.1.1.2.2.1) hh hv
  have haSome := firstHitSplit_eq_some a.1.1.1.reflectPrefix
    (reflectPrefix_firstHit a.1.1.1 a.1.1.2.1)
  have hbSome := firstHitSplit_eq_some b.1.1.1.reflectPrefix
    (reflectPrefix_firstHit b.1.1.1 b.1.1.2.1)
  have hsplits : a.1.1.1.reflectPrefix = b.1.1.1.reflectPrefix := by
    apply Option.some.inj
    rw [← haSome, ← hbSome, hsteps]
  have hfamilies :
      (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target)
          a.1.1 =
        (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target)
          b.1.1 := by
    apply Subtype.ext
    exact hsplits
  have habFamily : a.1.1 = b.1.1 :=
    (reflectPrefixFirstHitFamilyEquiv start (level : Int) walkLength target).injective
      hfamilies
  apply Subtype.ext
  apply Subtype.ext
  exact habFamily


end IsingDiagonalWalkHitSplit
end StatMech.Universality
