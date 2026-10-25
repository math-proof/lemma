/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection


namespace StatMech.Universality

def isingDiagonalWalkNext (start d : Int × Int) : Int × Int :=
  (start.1 + d.1, start.2 + d.2)


def isingDiagonalWalkFirstHitSplit? (start : Int × Int) (level : Int) :
    (path : List (Int × Int)) → Option (IsingDiagonalWalkHitSplit start level)
  | [] =>
      if h : start.1 = level then
        some ⟨[], [], by simpa [isingDiagonalWalkDisplacement] using h⟩
      else none
  | d :: path =>
      if h : start.1 = level then
        some ⟨[], d :: path, by simpa [isingDiagonalWalkDisplacement] using h⟩
      else
        match isingDiagonalWalkFirstHitSplit? (isingDiagonalWalkNext start d)
            level path with
        | none => none
        | some w => some ⟨d :: w.before, w.after, by
            have hw := w.hit
            unfold isingDiagonalWalkNext isingDiagonalWalkDisplacement at hw
            simp only [isingDiagonalWalkDisplacement, List.map_cons,
              List.sum_cons]
            dsimp at hw ⊢
            omega⟩

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def steps (w : IsingDiagonalWalkHitSplit start level) : List (Int × Int) :=
  w.before ++ w.after

end IsingDiagonalWalkHitSplit
end StatMech.Universality
