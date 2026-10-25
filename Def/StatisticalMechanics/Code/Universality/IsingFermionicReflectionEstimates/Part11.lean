/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part11


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def SurvivalExceptionalMirrorFamilyAll
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat) :=
  Σ target : Int × Int,
    SurvivalExceptionalMirrorFamily R start level walkLength target

def survivalExceptionalMirrorProjectionAll
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    SurvivalExceptionalMirrorFamilyAll R start (level : Int) walkLength →
      IsingLineChoicePathFamily level walkLength
          (leftGapNeighbor level hlevel) (leftGapLeft level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  survivalExceptionalMirrorProjection R level walkLength start w.1
    hstart hlevel w.2

end IsingDiagonalWalkHitSplit
end StatMech.Universality
