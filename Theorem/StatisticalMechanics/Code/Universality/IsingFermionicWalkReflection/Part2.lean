/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

theorem firstHitSplit_firstHit {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    w.FirstHit := by
  induction path generalizing start w with
  | nil =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        simp [FirstHit]
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        simp [FirstHit]
      · cases hrec : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path with
        | none => simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
        | some u =>
            simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
            subst w
            intro k hk
            cases k with
            | zero =>
                simpa [isingDiagonalWalkEndpoint,
                  isingDiagonalWalkDisplacement] using hs
            | succ k =>
                have hk' : k < u.before.length := by
                  simpa using hk
                have hu := ih (start := isingDiagonalWalkNext start d)
                  (w := u) hrec k hk'
                simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
                  isingDiagonalWalkDisplacement, add_assoc] using hu


theorem firstHitSplit_eq_some (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.FirstHit) :
    isingDiagonalWalkFirstHitSplit? start level w.steps = some w := by
  cases w with
  | mk before after hit =>
      induction before generalizing start with
      | nil =>
          have hs : start.1 = level := by
            simpa [isingDiagonalWalkDisplacement] using hit
          cases after <;> simp [steps, isingDiagonalWalkFirstHitSplit?, hs]
      | cons d before ih =>
          have hs : start.1 ≠ level := by
            have hzero := hw 0 (by simp)
            simpa [isingDiagonalWalkEndpoint,
              isingDiagonalWalkDisplacement] using hzero
          let u : IsingDiagonalWalkHitSplit
              (isingDiagonalWalkNext start d) level :=
            ⟨before, after, by
              unfold isingDiagonalWalkNext
              unfold isingDiagonalWalkDisplacement at hit ⊢
              simp only [List.map_cons, List.sum_cons] at hit ⊢
              omega⟩
          have hu : u.FirstHit := by
            intro k hk
            have hsucc := hw (k + 1) (by simpa using hk)
            simpa [u, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] using hsucc
          have hrec : isingDiagonalWalkFirstHitSplit?
              (isingDiagonalWalkNext start d) level u.steps = some u :=
            ih (start := isingDiagonalWalkNext start d) u.hit hu
          simp [steps] at hrec
          simp [steps, isingDiagonalWalkFirstHitSplit?, hs, hrec, u]

end IsingDiagonalWalkHitSplit
end StatMech.Universality
