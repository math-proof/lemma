/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part2


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

theorem firstHitSplit_steps {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    w.steps = path := by
  induction path generalizing start w with
  | nil =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        rfl
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        rfl
      · cases hrec : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path with
        | none => simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
        | some u =>
            simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
            subst w
            have hu := ih (start := isingDiagonalWalkNext start d)
              (w := u) hrec
            unfold steps at hu ⊢
            simp [hu]


end IsingDiagonalWalkHitSplit
end StatMech.Universality
