/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part6


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def SurvivalExceptionalFirstHitFamilyAll
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat) :=
  Σ target : Int × Int,
    SurvivalExceptionalFirstHitFamily R start level walkLength target

def survivalExceptionalProjectionAll
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    SurvivalExceptionalFirstHitFamilyAll R start (level : Int) walkLength →
      IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  survivalExceptionalProjection R level walkLength start w.1
    hstart hlevel hgap w.2

end IsingDiagonalWalkHitSplit
end StatMech.Universality
